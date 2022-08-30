//! Core language syntax.
use std::fmt;

use crate::ast::Id;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Icitness {
    Explicit,
    Implicit,
}

/// De Bruijn index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Idx(pub usize);

/// Core term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    /// A reference to a local variable.
    Local(Idx),
    /// A reference to a global variable.
    Global(Id),
    App(Box<Term>, Icitness, Box<Term>),
    Abs(Icitness, Box<Term>),
    /// The universe.
    Type,
    /// The dependent function type (`(x : A) -> B`).
    Pi(Icitness, Box<Type>, Box<Type>),

    Meta(MetaVar),
    /// Representation of a hole plugged with a meta variable.
    InsertedMeta(MetaVar, Vec<bool>),
}

pub type Type = Term;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MetaVar(pub usize);

impl fmt::Display for MetaVar {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "?{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Definition {
    Constant { name: String, ty: Type, value: Term },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Program {
    pub defs: Vec<Definition>,
}
