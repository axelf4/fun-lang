use crate::ast::Expr;
use std::collections::HashMap;
use std::error;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<'a> {
    Number(i32),
    Lambda(Env<'a>, &'a str, Expr<'a>),
}

#[derive(Debug)]
pub enum Error {
    UnknownVar,
    AppNotFun,
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Error::UnknownVar => write!(fmt, "unknown var"),
            &Error::AppNotFun => write!(fmt, "applied non-function value"),
        }
    }
}

impl error::Error for Error {}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Env<'a>(HashMap<&'a str, Value<'a>>);

impl<'a> Env<'a> {
    fn new() -> Self {
        Env(HashMap::new())
    }

    fn lookup(&self, id: &str) -> Option<Value<'a>> {
        self.0.get(id).cloned()
    }

    fn insert(&self, id: &'a str, value: Value<'a>) -> Self {
        let mut map = self.0.clone();
        map.insert(id, value);
        Env(map)
    }
}

pub fn eval<'a, 'env>(env: &'env Env<'a>, e: Expr<'a>) -> Result<Value<'a>, Error> {
    Ok(match e {
        Expr::Number(n) => Value::Number(n),
        Expr::Var(id) => env.lookup(&id).ok_or(Error::UnknownVar)?,
        Expr::App(a, b) => {
            if let Value::Lambda(env2, x, e) = eval(env, *a)? {
                eval(&env2.insert(x, eval(env, *b)?), e)?
            } else {
                return Err(Error::AppNotFun);
            }
        }
        Expr::Abs(x, e) => Value::Lambda(env.clone(), x, *e),
    })
}

mod tests {
    use super::*;

    #[test]
    fn test_eval_int_literal() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(eval(&Env::new(), Expr::Number(42))?, Value::Number(42));
        Ok(())
    }

    #[test]
    fn test_apply_id() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            eval(
                &Env::new(),
                Expr::App(
                    Box::new(Expr::Abs("x", Box::new(Expr::Var("x")))),
                    Box::new(Expr::Number(4))
                )
            )?,
            Value::Number(4)
        );
        Ok(())
    }
}
