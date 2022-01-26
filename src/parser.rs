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
use crate::ast::{prepend_arg, Term};
use crate::elaboration::Icitness::{self, *};
use crate::lexer::{self, Spanned, Token};
use itertools::{intersperse, Itertools as _};
use lalrpop_util::lalrpop_mod;
use petgraph::{
    graph::{Graph, NodeIndex},
    Direction,
};
use std::collections::HashMap;
use std::collections::HashSet;
use std::{error, fmt, iter};

use glr::{lalr, Grammar, Parser, Sppf, SppfNode, Symbol};

lalrpop_mod!(pub fun);

#[derive(Debug)]
pub enum Error<'input> {
    LalrpopError(lalrpop_util::ParseError<usize, Token<'input>, lexer::Error<'input>>),
    AmbiguousMixfix,
    MixfixError,
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
            MixfixError => write!(
                fmt,
                "failed to parse mixfix operator wrt. associativity/precedence"
            ),
            EmptyNamePart(s) => write!(
                fmt,
                "the operator ‘{}’ contains empty name parts that are not suffixes/prefixes",
                s
            ),
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
    op_parts: HashSet<&'input str>,
    op_names: HashSet<&'input str>,
}

impl<'input> PrecedenceGraph<'input> {
    fn new(g: Graph<Precedence<'input>, ()>) -> Self {
        let op_parts = g
            .node_weights()
            .flat_map(|p| &p.operators)
            .flat_map(|op| op.name_parts())
            .collect();
        let op_names = g
            .node_weights()
            .flat_map(|p| &p.operators)
            .map(|op| op.1)
            .collect();
        Self {
            g,
            op_parts,
            op_names,
        }
    }

    fn roots<'a>(&'a self) -> impl Iterator<Item = NodeIndex> + 'a {
        self.g.node_indices().filter(|&i| {
            self.g
                .neighbors_directed(i, Direction::Incoming)
                .next()
                .is_none()
        })
    }

    fn with_op<R>(
        &mut self,
        name: &'input str,
        f: impl FnOnce(&mut Self) -> R,
    ) -> Result<R, Error<'input>> {
        let op = if let Some(op) = Operator::from_str(Associativity::Non, name)? {
            op
        } else {
            return Ok(f(self));
        };
        let lvl = self.g.add_node(Precedence {
            operators: vec![op],
        });
        let existing_parts: Vec<_> = op
            .name_parts()
            .filter(|part| !self.op_parts.insert(part))
            .collect();
        let new_name = self.op_names.insert(name);

        let result = f(self);

        if new_name {
            self.op_names.remove(name);
        }
        existing_parts
            .into_iter()
            .for_each(|part| debug_assert!(self.op_parts.remove(part)));
        self.g.remove_node(lvl);

        Ok(result)
    }
}

struct MixfixParser<'input, 'a> {
    pg: &'a PrecedenceGraph<'input>,
    productions: Vec<Vec<Vec<Symbol>>>,
    num_nonterminals: usize,

    lvl_to_sym: HashMap<NodeIndex, Symbol>,
    str_to_sym: HashMap<&'input str, Symbol>,
    str_map: HashMap<Symbol, &'input str>,
}

const SYM_ROOT: Symbol = 0;
const SYM_JUXTAPOS: Symbol = 1;
const SYM_ATOM: Symbol = 2;

impl<'input: 'a, 'a> MixfixParser<'input, 'a> {
    fn new(pg: &'a PrecedenceGraph<'input>) -> Self {
        let num_nonterminals = /* start */ 1 + /* juxtaposition */ 1 + /* atom */ 1 + pg.g.node_indices().map(|node| {
            let child_count = pg.g.neighbors(node).count();
            pg.g[node].operators.len() + match child_count {
                0 => 1,
                1 => 1,
                // Otherwise we create a parent nonterminal for the
                // combination of successor levels.
                _ => 2,
            }
        }).sum::<usize>();

        let mut result = Self {
            pg,
            productions: Vec::with_capacity(num_nonterminals),
            num_nonterminals,

            lvl_to_sym: HashMap::new(),
            str_to_sym: HashMap::new(),
            str_map: HashMap::new(),
        };
        result.build();
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

    fn build(&mut self) {
        // Reserve symbols for root/juxtaposition/atom
        for _ in 0..3 {
            self.productions.push(Vec::new());
        }

        // Build the root
        self.productions[SYM_ROOT as usize] = self
            .pg
            .roots()
            .map(|node| vec![self.sym_for_lvl(node)])
            .collect();
        assert!(
            self.productions[SYM_ROOT as usize].len() > 0,
            "Some operator is required."
        );

        // Build atom
        self.productions[SYM_JUXTAPOS as usize] =
            vec![vec![SYM_JUXTAPOS, SYM_ATOM], vec![SYM_ATOM]];
        self.productions[SYM_ATOM as usize] = iter::once(vec![self.non_op_sym()])
            .chain(
                self.pg
                    .g
                    .node_weights()
                    .flat_map(|p| &p.operators)
                    .filter(|&op| op.0 == Closed)
                    .map(|op| {
                        intersperse(op.name_parts().map(|s| self.sym_for_str(s)), 0).collect()
                    }),
            )
            .collect();

        for node in self.pg.g.node_indices() {
            self.build_lvl(node);
        }
    }

    fn build_lvl(&mut self, node: NodeIndex) {
        let p = &self.pg.g[node];
        let sym = self.sym_for_lvl(node);

        let mut succs = self.pg.g.neighbors(node);
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
            let inner = intersperse(op.name_parts().map(|s| self.sym_for_str(s)), 0);
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

    fn as_grammar(&self) -> Grammar {
        Grammar {
            num_symbols: self.num_symbols(),
            nonterminals: &self.productions,
        }
    }

    fn rebuild_inner(
        &self,
        sppf: &Sppf,
        nodes: &[SppfNode],
        input: &mut impl Iterator<Item = (Icitness, Term<'input>)>,
        fix: Fixity,
    ) -> Result<Term<'input>, Error<'input>> {
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
        let f = Term::Var(self.pg.op_names.get(s.as_str()).unwrap());
        let e = nodes.iter().skip(1).step_by(2).try_fold(f, |e, &n| {
            input.next().unwrap();
            Ok::<_, Error<'input>>(Term::App(
                Box::new(e),
                Explicit,
                Box::new(self.rebuild(sppf, n, input)?.1),
            ))
        })?;
        input.next().unwrap();
        Ok(e)
    }

    fn rebuild(
        &self,
        sppf: &Sppf,
        node: SppfNode,
        input: &mut impl Iterator<Item = (Icitness, Term<'input>)>,
    ) -> Result<(Icitness, Term<'input>), Error<'input>> {
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
                    // TODO This will probably shit itself if the
                    // graph is not linear.
                    return Err(Error::AmbiguousMixfix);
                }
                children
            } else {
                &[]
            }
        };
        // TODO Make it an error to supply an implicit arg to an op
        match node.symbol(sppf) {
            Ok(SYM_ROOT) => self.rebuild(sppf, children[0], input),
            Ok(SYM_JUXTAPOS) => {
                let e = self.rebuild(sppf, children[0], input)?.1;
                Ok((
                    Explicit,
                    if let Some(&n) = children.get(1) {
                        let (i, e2) = self.rebuild(sppf, n, input)?;
                        Term::App(Box::new(e), i, Box::new(e2))
                    } else {
                        e
                    },
                ))
            }
            Ok(SYM_ATOM) => {
                // If closed
                if children.len() == 1 {
                    self.rebuild(sppf, children[0], input)
                } else {
                    self.rebuild_inner(sppf, children, input, Closed)
                        .map(|e| (Explicit, e))
                }
            }
            // Single term
            Ok(s) if s == self.non_op_sym() => Ok(input.next().unwrap()),
            // Otherwise, a precedence level
            Ok(_) => match children {
                [] => unreachable!(),
                [x] => self.rebuild(sppf, *x, input),
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
                                    sppf,
                                    &children[..children.len() - 1],
                                    input,
                                    fix,
                                )?;
                                let b = self.rebuild(sppf, *lst, input)?.1;
                                Term::App(Box::new(f), Explicit, Box::new(b))
                            }
                            Infix(_) => {
                                let a = self.rebuild(sppf, *fst, input)?.1;
                                let f = self.rebuild_inner(sppf, mid, input, fix)?;
                                let b = self.rebuild(sppf, *lst, input)?.1;
                                Term::App(Box::new(prepend_arg(f, a)), Explicit, Box::new(b))
                            }
                            Postfix => {
                                let a = self.rebuild(sppf, *fst, input)?.1;
                                let f = self.rebuild_inner(sppf, &children[1..], input, fix)?;
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

fn parse_mixfix<'input: 'a, 'a>(
    pg: &'a PrecedenceGraph<'input>,
    mut input: impl Iterator<Item = (Icitness, Term<'input>)> + Clone,
) -> Result<Term<'input>, Error<'input>> {
    let mixfix_parser = MixfixParser::new(pg);
    let grammar = mixfix_parser.as_grammar();
    // TODO Cache the parse table
    let table = lalr::Table::new(&grammar);
    let parser = Parser::new(&grammar, &table);

    // TODO Do not clone the expressions of the iterator
    let input_symbols = input.clone().map(|e| match e {
        (_, Term::Var(s)) => {
            if let Some(&sym) = mixfix_parser.str_to_sym.get(s) {
                sym
            } else {
                mixfix_parser.non_op_sym()
            }
        }
        _ => mixfix_parser.non_op_sym(),
    });
    let (sppf, root) = parser.parse(input_symbols).ok_or(Error::MixfixError)?;
    // Rebuild the tree
    Ok(mixfix_parser.rebuild(&sppf, root, &mut input)?.1)
}

fn prec_pass<'input, 'a>(
    g: &'a mut PrecedenceGraph<'input>,
    e: Term<'input>,
) -> Result<Term<'input>, Error<'input>> {
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
            .map(|(i, e)| prec_pass(g, e).map(|e| (i, e)))
            .collect::<Result<_, _>>()?;

            parse_mixfix(g, xs.into_iter().rev())?
        }
        Term::Abs(i, x, t) => {
            let t = g.with_op(x, |g| prec_pass(g, *t))??;
            Term::Abs(i, x, Box::new(t))
        }

        Term::Pi(x, a, b) => {
            let a = prec_pass(g, *a)?;
            let b = g.with_op(x, |g| prec_pass(g, *b))??;
            Term::Pi(x, Box::new(a), Box::new(b))
        }
    })
}

pub fn parse<'input, I>(input: I) -> Result<Term<'input>, Error<'input>>
where
    I: 'input,
    I: Iterator<Item = Spanned<Token<'input>, usize, lexer::Error<'input>>>,
{
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
    let mut prec_graph = PrecedenceGraph::new(g);

    let expr = *fun::TermParser::new().parse(input)?;
    prec_pass(&mut prec_graph, expr)
}

mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use std::error;
    use Term::*;

    #[test]
    fn test_parse_mixfix() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            parse(Lexer::new(r"1 + [ x ] (2 * 3) + 4 * 5"))?,
            App(
                Box::new(App(
                    Box::new(Var("_+_")),
                    Explicit,
                    Box::new(App(
                        Box::new(App(Box::new(Var("_+_")), Explicit, Box::new(Number(1)))),
                        Explicit,
                        Box::new(App(
                            Box::new(App(Box::new(Var("[_]_")), Explicit, Box::new(Var("x")))),
                            Explicit,
                            Box::new(App(
                                Box::new(App(Box::new(Var("_*_")), Explicit, Box::new(Number(2)))),
                                Explicit,
                                Box::new(Number(3))
                            ))
                        ))
                    ))
                )),
                Explicit,
                Box::new(App(
                    Box::new(App(Box::new(Var("_*_")), Explicit, Box::new(Number(4)))),
                    Explicit,
                    Box::new(Number(5))
                ))
            )
        );
        Ok(())
    }

    #[test]
    fn test_parse_omega() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            parse(Lexer::new(r"\x -> x x"))?,
            Abs(
                Explicit,
                "x",
                Box::new(App(Box::new(Var("x")), Explicit, Box::new(Var("x"))))
            )
        );
        Ok(())
    }

    #[test]
    fn test_parse_empty_layout() -> Result<(), Box<dyn error::Error>> {
        let expr = parse(Lexer::new("case 0 of"))?;
        assert_eq!(expr, Number(69));

        Ok(())
    }

    #[test]
    fn test_parse_bound_mixfix() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            parse(Lexer::new(r"\_⁻¹ -> x ⁻¹"))?,
            Abs(
                Explicit,
                "_⁻¹",
                Box::new(App(Box::new(Var("_⁻¹")), Explicit, Box::new(Var("x"))))
            )
        );
        Ok(())
    }

    #[test]
    fn test_parse_implicit_arg() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            parse(Lexer::new(r"0 + id {Type} Type"))?,
            App(
                Box::new(App(Box::new(Var("_+_")), Explicit, Box::new(Number(0)))),
                Explicit,
                Box::new(App(
                    Box::new(App(Box::new(Var("id")), Implicit, Box::new(Type))),
                    Explicit,
                    Box::new(Type)
                ))
            )
        );
        Ok(())
    }
}
