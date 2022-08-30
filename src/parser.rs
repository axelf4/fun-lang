/*!
Mixfix operator parser.

Parsing proceeds in two phases:

1. First, the whole file is parsed using the LALRPOP parser, with
   function applications - including operators - turned into plain
   lists of tokens.
2. Second, for every expression in the result of the previous step, it
   is determined what mixfix operators are in scope. This is used to
   construct a context-free grammar corresponding to the precedence
   graph. This grammar is fed into a GLR parser that produces its own
   syntax tree. Lastly we convert this syntax tree back into our
   representation.

Implicit arguments cannot be given to operators without using the long
form (e.g. _+_ {Type} 1 2).
*/
use crate::ast::{prepend_arg, Definition, Id, Program, Term};
use crate::core::Icitness::{self, *};
use crate::lexer::{self, Lexer, Spanned, Token};
use itertools::{intersperse, Itertools as _};
use lalrpop_util::lalrpop_mod;
use petgraph::{
    graph::{Graph, NodeIndex},
    Direction,
};
use self_cell::self_cell;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::{error, fmt, iter};

use glr::{lalr, Sppf, SppfNode, Symbol};

lalrpop_mod!(#[allow(clippy::all)] pub fun);

#[derive(Debug)]
pub enum Error<'input> {
    LalrpopError(lalrpop_util::ParseError<usize, Token<'input>, lexer::Error<'input>>),
    AmbiguousMixfix,
    BadMixfix,
    EmptyNamePart(&'input str),
}

impl<'input> From<lalrpop_util::ParseError<usize, Token<'input>, lexer::Error<'input>>>
    for Error<'input>
{
    fn from(x: lalrpop_util::ParseError<usize, Token<'input>, lexer::Error<'input>>) -> Self {
        Error::LalrpopError(x)
    }
}

impl<'input> fmt::Display for Error<'input> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            LalrpopError(e) => e.fmt(fmt),
            AmbiguousMixfix => write!(fmt, "term is ambiguous due to mixfix operators"),
            BadMixfix => write!(
                fmt,
                "failed to parse mixfix operator wrt. associativity/precedence"
            ),
            EmptyNamePart(s) => write!(fmt, "the operator ‘{}’ contains empty name parts", s),
        }
    }
}

impl<'input> error::Error for Error<'input> {}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Associativity {
    Left,
    #[allow(unused)]
    Right,
    Non,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Fixity {
    Closed,
    Prefix,
    Infix(Associativity),
    Postfix,
}

use Fixity::*;

#[derive(Clone, Copy, Debug)]
struct Operator<'a>(Fixity, &'a str);

impl<'a> Operator<'a> {
    fn from_str(assoc: Associativity, s: &'a str) -> Result<Option<Operator<'a>>, Error<'a>> {
        use Associativity::*;
        if s == "_" || s.contains("__") {
            return Err(Error::EmptyNamePart(s));
        }
        if !s.contains('_') {
            return Ok(None); // Not an operator
        }
        Ok(Some(match (s.starts_with('_'), assoc, s.ends_with('_')) {
            (true, _, true) => Self(Infix(assoc), s),
            (false, Non, true) => Self(Prefix, s),
            (true, Non, false) => Self(Postfix, s),
            (false, Non, false) => Self(Closed, s),
            _ => unreachable!("Non infix ops may not be associative"),
        }))
    }

    fn name_parts(&self) -> impl Iterator<Item = &'a str> {
        self.1.split('_').filter(|s| !s.is_empty())
    }
}

#[derive(Debug)]
struct Precedence<'input> {
    operators: Vec<Operator<'input>>,
}

struct PrecedenceGraph<'input> {
    g: Graph<Precedence<'input>, ()>,
    /// Lazily computed mixfix parser.
    parser: RefCell<Option<MixfixParser<'input>>>,
}

struct Roots<'a, N, E>(&'a Graph<N, E>, petgraph::graph::NodeIndices);

impl<'a, N, E> Iterator for Roots<'a, N, E> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let n = self.1.next()?;
            if self
                .0
                .neighbors_directed(n, Direction::Incoming)
                .next()
                .is_none()
            {
                return Some(n);
            }
        }
    }
}

impl<'w> PrecedenceGraph<'w> {
    fn new(g: Graph<Precedence<'w>, ()>) -> Self {
        Self {
            g,
            parser: RefCell::new(None),
        }
    }

    fn roots(&self) -> impl Iterator<Item = NodeIndex> + '_ {
        Roots(&self.g, self.g.node_indices())
    }

    fn parser(&self) -> RefMut<'_, MixfixParser<'w>> {
        RefMut::map(self.parser.borrow_mut(), |x| {
            x.get_or_insert_with(|| MixfixParser::from_prec_graph(self))
        })
    }

    fn add_op(&mut self, name: &'w str) -> Result<Option<NodeIndex>, Error<'w>> {
        let op = if let Some(op) = Operator::from_str(Associativity::Non, name)? {
            op
        } else {
            return Ok(None);
        };
        let lvl = self.g.add_node(Precedence {
            operators: vec![op],
        });
        Ok(Some(lvl))
    }

    fn with_op<R>(
        &mut self,
        name: &'w str,
        f: impl FnOnce(&mut Self) -> R,
    ) -> Result<R, Error<'w>> {
        let lvl = if let Some(x) = self.add_op(name)? {
            x
        } else {
            return Ok(f(self));
        };
        let old_parser = self.parser.replace(None);

        let result = f(self);

        *self.parser.borrow_mut() = old_parser;
        self.g.remove_node(lvl);

        Ok(result)
    }
}

impl Default for PrecedenceGraph<'_> {
    fn default() -> Self {
        use Associativity::*;

        let mut g = Graph::new();
        let lvl0 = g.add_node(Precedence {
            operators: vec![Operator::from_str(Left, "_+_").unwrap().unwrap()],
        });
        let lvl1 = g.add_node(Precedence {
            operators: vec![
                Operator::from_str(Left, "_*_").unwrap().unwrap(),
                Operator::from_str(Non, "[_]_").unwrap().unwrap(),
            ],
        });
        g.add_edge(lvl0, lvl1, ());
        Self::new(g)
    }
}

struct MixfixBuilder<'input> {
    productions: Vec<Vec<Vec<Symbol>>>,
    num_nonterminals: usize,

    lvl_to_sym: HashMap<NodeIndex, Symbol>,
    str_to_sym: HashMap<&'input str, Symbol>,
    str_map: HashMap<Symbol, &'input str>,
}

const SYM_ROOT: Symbol = 0;
const SYM_JUXTAPOS: Symbol = 1;
const SYM_ATOM: Symbol = 2;

impl<'input> MixfixBuilder<'input> {
    fn new<'a>(pg: &'a PrecedenceGraph<'input>) -> Self {
        let num_nonterminals = /* start */ 1 + /* juxtaposition */ 1 + /* atom */ 1 + pg.g.node_indices().map(|node| {
            let child_count = pg.g.neighbors(node).count();
            pg.g[node].operators.len() + match child_count {
                0 | 1 => 1,
                // Otherwise we create a parent nonterminal for the
                // combination of successor levels.
                _ => 2,
            }
        }).sum::<usize>();

        let mut result = Self {
            productions: Vec::with_capacity(num_nonterminals),
            num_nonterminals,

            lvl_to_sym: HashMap::new(),
            str_to_sym: HashMap::new(),
            str_map: HashMap::new(),
        };
        result.build(pg);
        result
    }

    fn non_op_sym(&self) -> Symbol {
        self.num_nonterminals as Symbol
    }

    fn num_symbols(&self) -> usize {
        self.num_nonterminals + 1 + self.str_to_sym.len()
    }

    fn sym_for_lvl(&mut self, p: NodeIndex) -> Symbol {
        *self.lvl_to_sym.entry(p).or_insert_with(|| {
            let sym = self.productions.len() as Symbol;
            self.productions.push(Vec::new());
            sym
        })
    }

    fn sym_for_str(&mut self, s: &'input str) -> Symbol {
        let next_sym = self.num_symbols() as Symbol;
        *self.str_to_sym.entry(s).or_insert_with(|| {
            self.str_map.insert(next_sym, s);
            next_sym
        })
    }

    fn as_grammar(&self) -> glr::Grammar {
        glr::Grammar {
            num_symbols: self.num_symbols(),
            nonterminals: &self.productions,
        }
    }

    fn build<'a>(&mut self, pg: &'a PrecedenceGraph<'input>) {
        // Reserve symbols for root/juxtaposition/atom
        for _ in SYM_ROOT..=SYM_ATOM {
            self.productions.push(Vec::new());
        }

        // Build the root
        self.productions[SYM_ROOT as usize] = pg
            .roots()
            .map(|node| vec![self.sym_for_lvl(node)])
            .collect();
        assert!(
            !self.productions[SYM_ROOT as usize].is_empty(),
            "Some operator is required."
        );

        // Build atom
        self.productions[SYM_JUXTAPOS as usize] =
            vec![vec![SYM_JUXTAPOS, SYM_ATOM], vec![SYM_ATOM]];
        self.productions[SYM_ATOM as usize] = iter::once(vec![self.non_op_sym()])
            .chain(
                pg.g.node_weights()
                    .flat_map(|p| &p.operators)
                    .filter(|&op| op.0 == Closed)
                    .map(|op| {
                        intersperse(op.name_parts().map(|s| self.sym_for_str(s)), SYM_ROOT)
                            .collect()
                    }),
            )
            .collect();

        for node in pg.g.node_indices() {
            self.build_lvl(pg, node);
        }
    }

    fn build_lvl<'a>(&mut self, pg: &'a PrecedenceGraph<'input>, node: NodeIndex) {
        let p = &pg.g[node];
        let sym = self.sym_for_lvl(node);

        let mut succs = pg.g.neighbors(node);
        // Nonterminal for higher precedence level
        let p_suc = if let Some(fst) = succs.next() {
            let p_fst = self.sym_for_lvl(fst);

            if let Some(snd) = succs.next() {
                let _p_snd = self.sym_for_lvl(snd);
                todo!()
            } else {
                p_fst
            }
        } else {
            SYM_JUXTAPOS
        };

        let mut prods = vec![vec![p_suc]];
        for op in &p.operators {
            let inner = intersperse(op.name_parts().map(|s| self.sym_for_str(s)), SYM_ROOT);
            prods.push(match op.0 {
                Closed => continue,
                Prefix => inner.chain(iter::once(sym)).collect(),
                Infix(Associativity::Left) => iter::once(sym)
                    .chain(inner)
                    .chain(iter::once(p_suc))
                    .collect(),
                Infix(Associativity::Right) => iter::once(p_suc)
                    .chain(inner)
                    .chain(iter::once(sym))
                    .collect(),
                Infix(Associativity::Non) => iter::once(p_suc)
                    .chain(inner)
                    .chain(iter::once(p_suc))
                    .collect(),
                Postfix => iter::once(sym).chain(inner).collect(),
            });
        }

        self.productions[sym as usize] = prods;
    }

    fn rebuild_inner<'a>(
        &self,
        db: &dyn crate::Db,
        pg: &'a PrecedenceGraph<'input>,
        sppf: &Sppf,
        nodes: &[SppfNode],
        input: &mut impl Iterator<Item = (Icitness, Term)>,
        fix: Fixity,
    ) -> Result<Term, Error<'input>> {
        let s = (if let Infix(_) | Postfix = fix {
            Some("")
        } else {
            None
        })
        .into_iter()
        .chain(
            nodes
                .iter()
                .step_by(2)
                .map(|n| self.str_map[&n.symbol(sppf).unwrap()]),
        )
        .chain(if let Prefix | Infix(_) = fix {
            Some("")
        } else {
            None
        })
        .join("_");
        let f = Term::Var(Id::new(db, s));
        let e = nodes.iter().skip(1).step_by(2).try_fold(f, |e, &n| {
            input.next().unwrap();
            Ok::<_, Error<'input>>(Term::App(
                Box::new(e),
                Explicit,
                Box::new(self.rebuild(db, pg, sppf, n, input)?.1),
            ))
        })?;
        input.next().unwrap();
        Ok(e)
    }

    fn rebuild<'a>(
        &self,
        db: &dyn crate::Db,
        pg: &'a PrecedenceGraph<'input>,
        sppf: &Sppf,
        node: SppfNode,
        input: &mut impl Iterator<Item = (Icitness, Term)>,
    ) -> Result<(Icitness, Term), Error<'input>> {
        let is_op_part = |n: SppfNode| {
            if let Ok(s) = n.symbol(sppf) {
                // If s is a terminal and not non_op
                s > self.num_nonterminals as Symbol
            } else {
                false
            }
        };
        let children = {
            let mut family = node.family(sppf);
            if let Some(children) = family.next() {
                if family.next().is_some() {
                    // TODO This will shit itself if the graph is not linear.
                    // TODO return Err(Error::AmbiguousMixfix);
                }
                children
            } else {
                &[]
            }
        };
        // TODO Make it an error to supply an implicit arg to an op
        match node.symbol(sppf) {
            Ok(SYM_ROOT) => self.rebuild(db, pg, sppf, children[0], input),
            Ok(SYM_JUXTAPOS) => {
                let e = self.rebuild(db, pg, sppf, children[0], input)?.1;
                Ok((
                    Explicit,
                    if let Some(&n) = children.get(1) {
                        let (i, e2) = self.rebuild(db, pg, sppf, n, input)?;
                        Term::App(Box::new(e), i, Box::new(e2))
                    } else {
                        e
                    },
                ))
            }
            Ok(SYM_ATOM) => {
                // If closed
                if children.len() == 1 {
                    self.rebuild(db, pg, sppf, children[0], input)
                } else {
                    self.rebuild_inner(db, pg, sppf, children, input, Closed)
                        .map(|e| (Explicit, e))
                }
            }
            // Single term
            Ok(s) if s == self.non_op_sym() => Ok(input.next().unwrap()),
            // Otherwise, a precedence level
            Ok(_) => match children {
                [] => unreachable!(),
                [x] => self.rebuild(db, pg, sppf, *x, input),
                [fst, mid @ .., lst] => {
                    let fix = match (is_op_part(*fst), is_op_part(*lst)) {
                        (false, false) => Infix(Associativity::Non),
                        (true, false) => Prefix,
                        (false, true) => Postfix,
                        (true, true) => Closed,
                    };
                    Ok((
                        Explicit,
                        match fix {
                            Prefix => {
                                let f = self.rebuild_inner(
                                    db,
                                    pg,
                                    sppf,
                                    &children[..children.len() - 1],
                                    input,
                                    fix,
                                )?;
                                let b = self.rebuild(db, pg, sppf, *lst, input)?.1;
                                Term::App(Box::new(f), Explicit, Box::new(b))
                            }
                            Infix(_) => {
                                let a = self.rebuild(db, pg, sppf, *fst, input)?.1;
                                let f = self.rebuild_inner(db, pg, sppf, mid, input, fix)?;
                                let b = self.rebuild(db, pg, sppf, *lst, input)?.1;
                                Term::App(Box::new(prepend_arg(f, a)), Explicit, Box::new(b))
                            }
                            Postfix => {
                                let a = self.rebuild(db, pg, sppf, *fst, input)?.1;
                                let f =
                                    self.rebuild_inner(db, pg, sppf, &children[1..], input, fix)?;
                                prepend_arg(f, a)
                            }
                            Closed => unreachable!(),
                        },
                    ))
                }
            },
            Err(_) => unreachable!(), // The grammar has no nullable symbols
        }
    }
}

type GlrGrammar<'grammar> = glr::Grammar<'grammar>;
type LalrTable<'grammar> = lalr::Table<'grammar>;

self_cell!(
    struct MixfixGrammar<'input> {
        owner: MixfixBuilder<'input>,
        #[covariant]
        dependent: GlrGrammar,
    }
);

self_cell!(
    struct MixfixParser<'input> {
        owner: MixfixGrammar<'input>,
        #[covariant]
        dependent: LalrTable,
    }
);

impl<'input> MixfixParser<'input> {
    fn from_prec_graph(pg: &PrecedenceGraph<'input>) -> Self {
        let builder = MixfixBuilder::new(pg);
        let mixfix_grammar = MixfixGrammar::new(builder, |builder| builder.as_grammar());
        Self::new(mixfix_grammar, |g| lalr::Table::new(g.borrow_dependent()))
    }

    fn parse(
        &self,
        db: &dyn crate::Db,
        pg: &PrecedenceGraph<'input>,
        mut input: impl Iterator<Item = (Icitness, Term)> + Clone,
    ) -> Result<Term, Error<'input>> {
        let builder = self.borrow_owner().borrow_owner();
        let grammar = builder.as_grammar();
        let table = self.borrow_dependent();
        let parser = glr::Parser::new(&grammar, table);

        // TODO Do not clone the expressions of the iterator
        let input_symbols = input.clone().map(|e| match e {
            (_, Term::Var(s)) => {
                if let Some(&sym) = builder.str_to_sym.get(s.text(db).as_str()) {
                    sym
                } else {
                    builder.non_op_sym()
                }
            }
            _ => builder.non_op_sym(),
        });
        let (sppf, root) = parser.parse(input_symbols).ok_or(Error::BadMixfix)?;
        // Rebuild the tree
        Ok(builder.rebuild(db, pg, &sppf, root, &mut input)?.1)
    }
}

fn prec_pass<'input, 'a>(
    db: &'input dyn crate::Db,
    pg: &'a mut PrecedenceGraph<'input>,
    e: Term,
) -> Result<Term, Error<'input>> {
    Ok(match e {
        Term::Number(_) | Term::Var(_) | Term::Type | Term::Hole => e,
        Term::App(_, _, _) => {
            // Unfold the left-recursive sequence
            let mut e = Some(e);
            let xs: Vec<_> = iter::from_fn(move || {
                Some(match e.take()? {
                    Term::App(next, i, item) => {
                        e = Some(*next);
                        (i, *item)
                    }
                    item => {
                        e = None;
                        (Explicit, item)
                    }
                })
            })
            .map(|(i, e)| prec_pass(db, pg, e).map(|e| (i, e)))
            .collect::<Result<_, _>>()?;

            pg.parser().parse(db, pg, xs.into_iter().rev())?
        }
        Term::Abs(i, x, t) => {
            let t = pg.with_op(x.text(db), |g| prec_pass(db, g, *t))??;
            Term::Abs(i, x, Box::new(t))
        }

        Term::Pi(i, x, a, b) => {
            let a = prec_pass(db, pg, *a)?;
            let b = if let Some(x) = x {
                pg.with_op(x.text(db), |g| prec_pass(db, g, *b))?
            } else {
                prec_pass(db, pg, *b)
            }?;
            Term::Pi(i, x, Box::new(a), Box::new(b))
        }
    })
}

pub fn parse_term<'input, I>(db: &'input dyn crate::Db, input: I) -> Result<Term, Error<'input>>
where
    I: Iterator<Item = Spanned<Token<'input>, usize, lexer::Error<'input>>>,
{
    let mut prec_graph = Default::default();
    let expr = *fun::TermParser::new().parse(db, input)?;
    prec_pass(db, &mut prec_graph, expr)
}

#[salsa::input]
pub struct ProgramSource {
    #[return_ref]
    text: String,
}

#[salsa::tracked]
pub fn parse_program(db: &dyn crate::Db, s: ProgramSource) -> Result<Program, String> {
    let input = Lexer::new(s.text(db)).open_layout();
    let defs = fun::ProgramParser::new()
        .parse(db, input)
        .map_err(|e| e.to_string())?;
    let mut prec_graph = PrecedenceGraph::default();
    for Definition::Constant { name, .. } in &defs {
        prec_graph
            .add_op(name.text(db))
            .map_err(|e| e.to_string())?;
    }
    let defs = defs
        .into_iter()
        .map(|def| match def {
            Definition::Constant { name, ty, value } => {
                let ty = ty
                    .map(|term| prec_pass(db, &mut prec_graph, term))
                    .transpose()?;
                let value = prec_pass(db, &mut prec_graph, value)?;
                Ok((name, Definition::Constant { name, ty, value }))
            }
        })
        .collect::<Result<_, Error>>()
        .map_err(|e| e.to_string())?;
    Ok(Program::new(db, defs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use Term::*;

    #[test]
    fn test_parse_mixfix() {
        let db = crate::db::Database::default();
        assert_eq!(
            parse_term(&db, Lexer::new(r"1 + [ x ] (2 * 3) + 4 * 5")).unwrap(),
            App(
                Box::new(App(
                    Box::new(Var(Id::new(&db, "_+_".into()))),
                    Explicit,
                    Box::new(App(
                        Box::new(App(
                            Box::new(Var(Id::new(&db, "_+_".into()))),
                            Explicit,
                            Box::new(Number(1))
                        )),
                        Explicit,
                        Box::new(App(
                            Box::new(App(
                                Box::new(Var(Id::new(&db, "[_]_".into()))),
                                Explicit,
                                Box::new(Var(Id::new(&db, "x".into())))
                            )),
                            Explicit,
                            Box::new(App(
                                Box::new(App(
                                    Box::new(Var(Id::new(&db, "_*_".into()))),
                                    Explicit,
                                    Box::new(Number(2))
                                )),
                                Explicit,
                                Box::new(Number(3))
                            ))
                        ))
                    ))
                )),
                Explicit,
                Box::new(App(
                    Box::new(App(
                        Box::new(Var(Id::new(&db, "_*_".into()))),
                        Explicit,
                        Box::new(Number(4))
                    )),
                    Explicit,
                    Box::new(Number(5))
                ))
            )
        );
    }

    #[test]
    fn test_parse_omega() {
        let db = crate::db::Database::default();
        assert_eq!(
            parse_term(&db, Lexer::new(r"\x -> x x")).unwrap(),
            Abs(
                Explicit,
                Id::new(&db, "x".into()),
                Box::new(App(
                    Box::new(Var(Id::new(&db, "x".into()))),
                    Explicit,
                    Box::new(Var(Id::new(&db, "x".into())))
                ))
            )
        );
    }

    #[test]
    fn test_parse_empty_layout() {
        let db = crate::db::Database::default();
        let expr = parse_term(&db, Lexer::new("case 0 of")).unwrap();
        assert_eq!(expr, Number(69));
    }

    #[test]
    fn test_parse_bound_postfix() {
        let db = crate::db::Database::default();
        assert_eq!(
            parse_term(&db, Lexer::new(r"\_⁻¹ -> x ⁻¹")).unwrap(),
            Abs(
                Explicit,
                Id::new(&db, "_⁻¹".into()),
                Box::new(App(
                    Box::new(Var(Id::new(&db, "_⁻¹".into()))),
                    Explicit,
                    Box::new(Var(Id::new(&db, "x".into())))
                ))
            )
        );
    }

    #[test]
    fn test_parse_implicit_arg() {
        let db = crate::db::Database::default();
        assert_eq!(
            parse_term(&db, Lexer::new(r"0 + id {Type} Type")).unwrap(),
            App(
                Box::new(App(
                    Box::new(Var(Id::new(&db, "_+_".into()))),
                    Explicit,
                    Box::new(Number(0))
                )),
                Explicit,
                Box::new(App(
                    Box::new(App(
                        Box::new(Var(Id::new(&db, "id".into()))),
                        Implicit,
                        Box::new(Type)
                    )),
                    Explicit,
                    Box::new(Type)
                ))
            )
        );
    }
}
