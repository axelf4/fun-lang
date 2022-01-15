/// Raw syntax.

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term<'input> {
    /// The universe.
    Type,
    Number(i32),
    // TODO Rename to Id
    Var(&'input str),
    App(Box<Term<'input>>, Box<Term<'input>>),
    Abs(&'input str, Box<Term<'input>>),
    /// The dependent function type (`(x : A) -> B`).
    Pi(&'input str, Box<Term<'input>>, Box<Term<'input>>),
    /// `_`.
    #[allow(unused)]
    Hole,
}
