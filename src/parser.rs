/// Mixfix expression parser.
use crate::ast::Expr;
use crate::lexer::{self, Spanned, Token};
use lalrpop_util::lalrpop_mod;
use std::iter;

use nom::branch::alt;
use nom::combinator::eof;
use nom::multi::many1;
use nom::sequence::terminated;
use nom::IResult;
use nom::Parser as _;

lalrpop_mod!(pub fun);

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

#[derive(Debug)]
struct Operator<'a>(Fixity, &'a str);

impl<'a> Operator<'a> {
    fn from_str(assoc: Associativity, s: &'a str) -> Option<Operator<'a>> {
        use Associativity::*;
        if s.contains("__") {
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

type PrecedenceGraph<'input> = [Precedence<'input>];

#[derive(Clone, Debug)]
struct Input<'input, 'a>(&'a [Expr<'input>]);

impl<'input, 'a> nom::InputLength for Input<'input, 'a> {
    fn input_len(&self) -> usize {
        self.0.len()
    }
}

fn expr_where<'input: 'a, 'a, F>(
    f: F,
) -> impl FnMut(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Expr<'input>>
where
    F: Fn(&Expr<'a>) -> bool,
{
    move |i| match i.0.split_first() {
        Some((e, rest)) if f(e) => Ok((Input(rest), e.clone())),
        _ => Err(nom::Err::Error(nom::error::Error {
            input: i,
            code: nom::error::ErrorKind::Tag,
        })),
    }
}

#[derive(Clone)]
struct AltIter<I>(I);

impl<I> AltIter<I> {
    fn alt_parse<Input, Output, Error>(self, input: Input) -> IResult<Input, Output, Error>
    where
        Input: Clone,
        I: Iterator,
        I::Item: nom::Parser<Input, Output, Error>,
        Error: nom::error::ParseError<Input>,
    {
        let mut e: Option<Error> = None;
        for mut p in self.0 {
            match p.parse(input.clone()) {
                Err(nom::Err::Error(e2)) => match e {
                    Some(e1) => {
                        e = Some(e1.or(e2));
                    }
                    None => {
                        e = Some(e2);
                    }
                },
                res => return res,
            }
        }
        Err(nom::Err::Error(e.unwrap_or(Error::from_error_kind(
            input,
            nom::error::ErrorKind::Fail,
        ))))
    }
}

impl<I, Input, O, E> nom::branch::Alt<Input, O, E> for AltIter<I>
where
    Input: Clone,
    E: nom::error::ParseError<Input>,
    I: Iterator + Clone,
    I::Item: nom::Parser<Input, O, E>,
{
    fn choice(&mut self, input: Input) -> IResult<Input, O, E> {
        self.clone().alt_parse(input)
    }
}

fn expr<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Expr<'input>> {
    precs(prec_graph, prec_graph)
}

fn precs<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
    ps: &'a [Precedence<'input>],
) -> impl Fn(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Expr<'input>> {
    |i| {
        let mut atom = many1(expr_where(Expr::is_not_op)).map(|mut xs| {
            let e = xs.pop().expect("many1 did not parse 1 element?");
            xs.into_iter()
                .rev()
                .fold(e, |acc, f| Expr::App(Box::new(f), Box::new(acc)))
        });
        if ps.is_empty() {
            atom.parse(i)
        } else {
            alt(AltIter(ps.into_iter().map(|p| prec(prec_graph, p))))(i)
        }
    }
}

impl<'input> Expr<'input> {
    fn is_not_op(&self) -> bool {
        // TODO
        match self {
            Expr::Var(s) => !(s == &"+" || s == &"*" || s == &"[" || s == &"]"),
            _ => true,
        }
    }
}

fn prec<'input: 'a, 'a>(
    prec_graph: &'a PrecedenceGraph<'input>,
    p: &'a Precedence<'input>,
) -> impl FnMut(Input<'input, 'a>) -> IResult<Input<'input, 'a>, Expr<'input>> + 'a {
    move |i| {
        // Match a single specific identifier token
        let ident = |s| {
            expr_where(move |e| {
                if let Expr::Var(id) = e {
                    *id == s
                } else {
                    false
                }
            })
        };

        let inner_at_fix = |fix| {
            move |i| {
                let ops = p.operators.iter().filter(move |Operator(f, _)| f == &fix);

                AltIter(ops.map(|op @ Operator(_, s)| {
                    move |i| {
                        let mut res = Expr::Var(s);
                        let mut name_parts = op.name_parts();

                        let (mut i, _) = ident(name_parts.next().unwrap())(i)?;

                        while let Some(s) = name_parts.next() {
                            let (i2, e) = expr(prec_graph)(i)?;
                            let (i2, _) = ident(s)(i2)?;
                            res = Expr::App(Box::new(res), Box::new(e));
                            i = i2;
                        }

                        Ok((i, res))
                    }
                }))
                .alt_parse(i)
            }
        };

        let p_suc = precs(prec_graph, &p.sucs);

        fn prepend_arg<'input>(f: Expr<'input>, e: Expr<'input>) -> Expr<'input> {
            match f {
                Expr::App(f, e2) => Expr::App(Box::new(Expr::App(f, Box::new(e))), e2),
                _ => Expr::App(Box::new(f), Box::new(e)),
            }
        }

        let infix_non = |i| {
            let (i, el) = p_suc(i)?;
            let (i, f) = inner_at_fix(Infix(Associativity::Non))(i)?;
            let (i, er) = p_suc(i)?;
            Ok((i, Expr::App(Box::new(prepend_arg(f, el)), Box::new(er))))
        };

        let x = alt((
            inner_at_fix(Fixity::Closed),
            infix_non,
            |i| {
                let pre_right = alt((inner_at_fix(Fixity::Prefix), |i| {
                    let (i, e) = p_suc(i)?;
                    let (i, f) = inner_at_fix(Fixity::Infix(Associativity::Right))(i)?;
                    Ok((i, prepend_arg(f, e)))
                }));

                let (i, fs) = many1(pre_right)(i)?;
                let (i, e) = p_suc(i)?;
                Ok((
                    i,
                    fs.into_iter()
                        .rev()
                        .fold(e, |acc, f| Expr::App(Box::new(f), Box::new(acc))),
                ))
            },
            |i| {
                let post_left = alt((inner_at_fix(Fixity::Postfix).map(|_| todo!()), |i| {
                    let (i, f) = inner_at_fix(Fixity::Infix(Associativity::Left))(i)?;
                    let (i, er) = p_suc(i)?;
                    Ok((i, (f, Some(er))))
                }));

                let (i, e) = p_suc(i)?;
                let (i, fs) = many1(post_left)(i)?;
                Ok((
                    i,
                    fs.into_iter().fold(e, |acc, (f, er)| {
                        let a = prepend_arg(f, acc);
                        if let Some(e) = er {
                            Expr::App(Box::new(a), Box::new(e))
                        } else {
                            a
                        }
                    }),
                ))
            },
            |i| p_suc(i),
        ))(i);
        x
    }
}

fn prec_pass<'input, 'a>(g: &'a PrecedenceGraph<'input>, e: Expr<'input>) -> Expr<'input> {
    match e {
        Expr::Number(_) => e,
        Expr::Var(_) => e,
        Expr::App(_, _) => {
            // Unfold the left-recursive sequence
            let mut e = Some(e);
            let mut xs = iter::from_fn(move || {
                Some(match e.take()? {
                    Expr::App(next, item) => {
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
            .collect::<Vec<_>>();
            xs.reverse();

            let result = terminated(expr(g), eof)(Input(&xs))
                .expect("Failed to parse operator precedence")
                .1;
            result
        }
        Expr::Abs(id, mut body) => {
            take_mut::take(body.as_mut(), |e| prec_pass(g, e));
            Expr::Abs(id, body)
        }
    }
}

fn parse<'input, I>(
    input: I,
) -> Result<Expr<'input>, lalrpop_util::ParseError<usize, Token<'input>, lexer::Error>>
where
    I: 'input,
    I: Iterator<Item = Spanned<Token<'input>, usize, lexer::Error>>,
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
    let prec_forest = [prec_tree];

    let expr = *fun::ExprParser::new().parse(input)?;
    Ok(prec_pass(&prec_forest, expr))
}

mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use std::error;
    use Expr::*;

    #[test]
    fn test_parse_mixfix() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            parse(Lexer::new(r"1 + [ x ] (2 * 3) + 4 * 5"))?,
            App(
                Box::new(App(
                    Box::new(Var("_+_")),
                    Box::new(App(
                        Box::new(App(Box::new(Var("_+_")), Box::new(Number(1)))),
                        Box::new(App(
                            Box::new(App(Box::new(Var("[_]_")), Box::new(Var("x")))),
                            Box::new(App(
                                Box::new(App(Box::new(Var("_*_")), Box::new(Number(2)))),
                                Box::new(Number(3))
                            ))
                        ))
                    ))
                )),
                Box::new(App(
                    Box::new(App(Box::new(Var("_*_")), Box::new(Number(4)))),
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
            Abs("x", Box::new(App(Box::new(Var("x")), Box::new(Var("x")))))
        );
        Ok(())
    }

    #[test]
    fn test_parse_empty_layout() -> Result<(), Box<dyn error::Error>> {
        let expr = parse(Lexer::new("case 0 of"))?;
        assert_eq!(expr, Number(69));

        Ok(())
    }
}