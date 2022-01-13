#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term<'input> {
    Number(i32),
    // TODO Rename to Id
    Var(&'input str),
    App(Box<Term<'input>>, Box<Term<'input>>),
    Abs(&'input str, Box<Term<'input>>),
}
