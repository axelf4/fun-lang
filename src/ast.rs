/// Raw syntax.
use crate::core::Icitness::{self, *};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term<'input> {
    /// The universe.
    Type,
    Number(i32),
    // TODO Rename to Id
    Var(&'input str),
    App(Box<Term<'input>>, Icitness, Box<Term<'input>>),
    Abs(Icitness, &'input str, Box<Term<'input>>),
    Pi(&'input str, Box<Term<'input>>, Box<Term<'input>>),
    /// `_`.
    #[allow(unused)]
    Hole,
}

pub fn prepend_arg<'input>(f: Term<'input>, e: Term<'input>) -> Term<'input> {
    match f {
        Term::App(f, Explicit, e2) => {
            Term::App(Box::new(Term::App(f, Explicit, Box::new(e))), Explicit, e2)
        }
        _ => Term::App(Box::new(f), Explicit, Box::new(e)),
    }
}
