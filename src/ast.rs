#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr<'input> {
    Number(i32),
    Var(&'input str),
    App(Box<Expr<'input>>, Box<Expr<'input>>),
    Abs(&'input str, Box<Expr<'input>>),
}
