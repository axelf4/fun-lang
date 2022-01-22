/// Mixfix operator parser.
use crate::ast::Term;
use crate::elaboration::Icitness::*;
use crate::lexer::{self, Spanned, Token};
use lalrpop_util::lalrpop_mod;
use std::collections::HashSet;
use std::{error, fmt, iter, slice};

use nom::IResult;
use nom::Parser as _;
use nom::{
    branch::alt,
    combinator::{all_consuming, verify},
    multi::{fold_many1, many1},
    sequence::terminated,
};

lalrpop_mod!(pub fun);

#[derive(Debug)]
pub enum Error<'input> {
    LalrpopError(lalrpop_util::ParseError<usize, Token<'input>, lexer::Error<'input>>),
    MixfixError,
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
        match self {
            Error::LalrpopError(e) => e.fmt(fmt),
            Error::MixfixError => write!(
                fmt,
                "failed to parse mixfix operator wrt. associativity/precedence"
            ),
        }
    }
}

impl<'input> error::Error for Error<'input> {}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Associativity {
    Left,
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
    fn from_str(assoc: Associativity, s: &'a str) -> Option<Operator<'a>> {
        use Associativity::*;
        if s == "_" || s.contains("__") {
            return None;
        }
        Some(match (s.starts_with('_'), assoc, s.ends_with('_')) {
            (true, _, true) => Self(Infix(assoc), s),
            (false, Non, true) => Self(Prefix, s),
            (true, Non, false) => Self(Postfix, s),
            (false, Non, false) => Self(Closed, s),
            _ => return None,
        })
    }

    fn name_parts(&self) -> impl Iterator<Item = &'a str> {
        self.1.split('_').filter(|s| !s.is_empty())
    }
}

struct Precedence<'input> {
    operators: Vec<Operator<'input>>,
    sucs: Vec<Precedence<'input>>,
}

struct PrecedenceGraph<'input> {
    roots: Vec<Precedence<'input>>,
    op_parts: HashSet<&'input str>,
}

impl<'input> PrecedenceGraph<'input> {
    fn new(roots: Vec<Precedence<'input>>) -> Self {
        let mut result = Self {
            roots,
            op_parts: Default::default(),
        };
        result.op_parts = result
            .nodes()
            .flat_map(|p| &p.operators)
            .flat_map(|op| op.name_parts())
            .collect();
        result
    }

    /// Returns an iterator of all nodes in this graph.
    fn nodes(&self) -> impl Iterator<Item = &Precedence<'input>> {
        let mut x = vec![self.roots.iter()];
        iter::from_fn(move || {
            let item = loop {
                if let Some(item) = x.last_mut()?.next() {
                    break item;
                } else {
                    x.pop();
                }
            };
            x.push(item.sucs.iter());
            Some(item)
        })
    }

    fn non_op<'a>(
        &'a self,
    ) -> impl FnMut(Input<'input, 'a>) -> IResult<Input<'input, 'a>, &'a Term<'input>> {
        verify(single_expr(), |e| {
            if let Term::Var(s) = e {
                !self.op_parts.contains(s)
            } else {
                true
            }
        })
    }

    fn with_op<R>(&mut self, name: &'input str, f: impl FnOnce(&mut Self) -> R) -> R {
        let op = if let Some(op) = Operator::from_str(Associativity::Non, name) {
            op
        } else {
            return f(self);
        };
        self.roots.push(Precedence {
            operators: vec![op],
            sucs: Vec::new(),
        });
        let existing_parts: Vec<_> = op
            .name_parts()
            .filter(|part| !self.op_parts.insert(part))
            .collect();

        let result = f(self);

        existing_parts
            .into_iter()
            .for_each(|part| debug_assert!(self.op_parts.remove(part)));
        self.roots.pop();

        result
    }
}

#[derive(Clone, Debug)]
struct Input<'input, 'a>(iter::Rev<slice::Iter<'a, Term<'input>>>);

impl<'input, 'a> nom::InputLength for Input<'input, 'a> {
    fn input_len(&self) -> usize {
        self.0.size_hint().0
    }
}

/// Returns a parser for a single expression token.
fn single_expr<'input: 'a, 'a>(
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, &'a Term<'input>> {
    move |i| {
        let mut i2 = i.clone();
        match i2.0.next() {
            Some(x) => Ok((i2, x)),
            _ => Err(nom::Err::Error(nom::error::Error {
                input: i,
                code: nom::error::ErrorKind::Tag,
            })),
        }
    }
}

fn alt_iter<I, Input, Output, Error>(iter: I) -> impl FnOnce(Input) -> IResult<Input, Output, Error>
where
    Input: Clone,
    I: Iterator,
    I::Item: nom::Parser<Input, Output, Error>,
    Error: nom::error::ParseError<Input>,
{
    |i| {
        let mut e: Option<Error> = None;
        for mut p in iter {
            match p.parse(i.clone()) {
                Err(nom::Err::Error(e2)) => e = Some(if let Some(e1) = e { e1.or(e2) } else { e2 }),
                res => return res,
            }
        }
        Err(nom::Err::Error(e.unwrap_or(Error::from_error_kind(
            i,
            nom::error::ErrorKind::Alt,
        ))))
    }
}

fn expr<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Term<'input>> {
    precs(prec_graph, &prec_graph.roots)
}

fn precs<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
    ps: &'a [Precedence<'input>],
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Term<'input>> {
    |i| {
        let op_closed = |i| {
            alt_iter(
                prec_graph
                    .nodes()
                    .map(|p| inner_at_fix(prec_graph, p, Closed)),
            )(i)
        };
        let mut atom =
            many1(alt((prec_graph.non_op().map(Clone::clone), op_closed))).map(|mut xs| {
                let e = xs.pop().expect("many1 did not parse 1 element?");
                xs.into_iter()
                    .rev()
                    .fold(e, |acc, f| Term::App(Box::new(f), Explicit, Box::new(acc)))
            });
        if ps.is_empty() {
            atom.parse(i)
        } else {
            alt_iter(ps.into_iter().map(|p| prec(prec_graph, p)))(i)
        }
    }
}

fn inner_at_fix<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
    p: &'a Precedence<'input>,
    fix: Fixity,
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Term<'input>> {
    // Match a single specific identifier token
    let ident = |id| verify(single_expr(), move |&e: &&Term<'input>| e == &Term::Var(id));

    move |i| {
        let ops = p.operators.iter().filter(move |Operator(f, _)| f == &fix);

        alt_iter(ops.map(|op @ Operator(_, s)| {
            move |i| {
                let mut res = Term::Var(s);
                let mut name_parts = op.name_parts();

                let (mut i, _) = ident(name_parts.next().unwrap())(i)?;
                while let Some(s) = name_parts.next() {
                    let (i2, e) = terminated(expr(prec_graph), ident(s))(i)?;
                    res = Term::App(Box::new(res), Explicit, Box::new(e));
                    i = i2;
                }

                Ok((i, res))
            }
        }))(i)
    }
}

/// Parser for an expression at some precedence level.
fn prec<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
    p: &'a Precedence<'input>,
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Term<'input>> + 'a {
    move |i| {
        let p_suc = precs(prec_graph, &p.sucs); // TODO Memoize

        fn prepend_arg<'input>(f: Term<'input>, e: Term<'input>) -> Term<'input> {
            match f {
                Term::App(f, i, e2) => {
                    Term::App(Box::new(Term::App(f, Explicit, Box::new(e))), Explicit, e2)
                }
                _ => Term::App(Box::new(f), Explicit, Box::new(e)),
            }
        }

        let x = alt((
            |i| {
                let (i, el) = p_suc(i)?;
                let (i, f) = inner_at_fix(prec_graph, p, Infix(Associativity::Non))(i)?;
                let (i, er) = p_suc(i)?;
                Ok((
                    i,
                    Term::App(Box::new(prepend_arg(f, el)), Explicit, Box::new(er)),
                ))
            },
            |i| {
                let pre_right = alt((inner_at_fix(prec_graph, p, Prefix), |i| {
                    let (i, e) = p_suc(i)?;
                    let (i, f) = inner_at_fix(prec_graph, p, Infix(Associativity::Right))(i)?;
                    Ok((i, prepend_arg(f, e)))
                }));

                let (i, fs) = many1(pre_right)(i)?;
                let (i, e) = p_suc(i)?;
                Ok((
                    i,
                    fs.into_iter()
                        .rev()
                        .fold(e, |acc, f| Term::App(Box::new(f), Explicit, Box::new(acc))),
                ))
            },
            |i| {
                let post_left = alt((
                    inner_at_fix(prec_graph, p, Postfix).map(|f| (f, None)),
                    |i| {
                        let (i, f) = inner_at_fix(prec_graph, p, Infix(Associativity::Left))(i)?;
                        let (i, er) = p_suc(i)?;
                        Ok((i, (f, Some(er))))
                    },
                ));

                let (i, e) = p_suc(i)?;
                let mut e = Some(e);
                let x = fold_many1(
                    post_left,
                    || e.take().unwrap(),
                    |acc, (f, er)| {
                        let a = prepend_arg(f, acc);
                        if let Some(e) = er {
                            Term::App(Box::new(a), Explicit, Box::new(e))
                        } else {
                            a
                        }
                    },
                )(i);
                x
            },
            |i| p_suc(i),
        ))(i);
        x
    }
}

fn prec_pass<'input, 'a>(
    g: &'a mut PrecedenceGraph<'input>,
    e: Term<'input>,
) -> Result<Term<'input>, Error<'input>> {
    Ok(match e {
        Term::Number(_) | Term::Var(_) | Term::Type | Term::Hole => e,
        Term::App(_, i, _) => {
            assert!(i == Explicit);
            // Unfold the left-recursive sequence
            let mut e = Some(e);
            let xs: Vec<_> = iter::from_fn(move || {
                Some(match e.take()? {
                    Term::App(next, i, item) => {
                        assert!(i == Explicit); // TODO
                        e = Some(*next);
                        *item
                    }
                    item => {
                        e = None;
                        item
                    }
                })
            })
            .map(|e| prec_pass(g, e))
            .collect::<Result<_, _>>()?;

            let (_i, e) =
                alt_iter(g.roots.iter().map(|p| all_consuming(prec(g, p))))(Input(xs.iter().rev()))
                    .map_err(|_e| Error::MixfixError)?;
            e
        }
        Term::Abs(i, x, t) => {
            let t = g.with_op(x, |g| prec_pass(g, *t))?;
            Term::Abs(i, x, Box::new(t))
        }

        Term::Pi(x, a, b) => {
            let a = prec_pass(g, *a)?;
            let b = g.with_op(x, |g| prec_pass(g, *b))?;
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

    let prec_tree = Precedence {
        operators: vec![Operator::from_str(Left, "_+_").unwrap()],
        sucs: vec![Precedence {
            operators: vec![
                Operator::from_str(Left, "_*_").unwrap(),
                Operator::from_str(Non, "[_]_").unwrap(),
            ],
            sucs: Vec::new(),
        }],
    };
    let mut prec_graph = PrecedenceGraph::new(vec![prec_tree]);

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
            // parse(Lexer::new(r"\_⁻¹ -> [ x ⁻¹ ] 3"))?,
            Abs(
                Explicit,
                "_⁻¹",
                Box::new(App(Box::new(Var("_⁻¹")), Explicit, Box::new(Var("x"))))
            )
        );
        Ok(())
    }
}
