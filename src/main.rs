use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub fun);

mod ast;
mod interpreter;
mod typecheck;

mod tests {
    use super::*;
    use ast::Expr;
    use std::error;

    #[test]
    fn test_parse_omega() -> Result<(), Box<dyn error::Error>> {
        let expr = fun::ExprParser::new().parse("\\x -> x x")?;
        assert_eq!(
            expr,
            Box::new(Expr::Abs(
                "x",
                Box::new(Expr::App(
                    Box::new(Expr::Var("x")),
                    Box::new(Expr::Var("x"))
                ))
            ))
        );

        Ok(())
    }
}

fn main() {
    println!("Hello, world!");
}
