use std::collections::HashMap;

/// Raw syntax.
use crate::core::Icitness::{self, *};

#[salsa::interned]
pub struct Id {
    #[return_ref]
    text: String,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Type,
    Number(i32),
    Var(Id),
    App(Box<Term>, Icitness, Box<Term>),
    Abs(Icitness, Id, Box<Term>),
    Pi(Icitness, Option<Id>, Box<Term>, Box<Term>),
    /// `_`.
    #[allow(unused)]
    Hole,
}

pub fn prepend_arg(f: Term, e: Term) -> Term {
    match f {
        Term::App(f, Explicit, e2) => {
            Term::App(Box::new(Term::App(f, Explicit, Box::new(e))), Explicit, e2)
        }
        _ => Term::App(Box::new(f), Explicit, Box::new(e)),
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Definition {
    Constant {
        name: Id,
        ty: Option<Term>,
        value: Term,
    },
}

#[salsa::tracked]
pub struct Program {
    #[return_ref]
    pub defs: HashMap<Id, Definition>,
}
