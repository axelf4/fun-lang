//! Core language syntax.
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Icitness {
    Explicit,
    Implicit,
}

/// De Bruijn index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ix(pub usize);

/// Core term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    /// A local variable.
    LocalVar(Ix),
    App(Box<Term>, Icitness, Box<Term>),
    Abs(Icitness, Box<Term>),
    /// The universe.
    Type,
    Pi(Icitness, Box<Type>, Box<Type>),
    Meta(MetaVar),
    /// Representation of a hole plugged with a meta.
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
