#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr<'a> {
    Number(i32),
    Var(&'a str),
    App(Box<Expr<'a>>, Box<Expr<'a>>),
    Abs(&'a str, Box<Expr<'a>>),
}
