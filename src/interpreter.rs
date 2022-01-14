use crate::ast::Term;
use std::collections::HashMap;
use std::error;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Value<'input> {
    Number(i32),
    Lambda(Env<'input>, &'input str, Term<'input>),
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
pub struct Env<'input>(HashMap<&'input str, Value<'input>>);

impl<'input> Env<'input> {
    fn new() -> Self {
        Env(HashMap::new())
    }

    fn lookup(&self, id: &str) -> Option<Value<'input>> {
        self.0.get(id).cloned()
    }

    fn insert(&self, id: &'input str, value: Value<'input>) -> Self {
        let mut map = self.0.clone();
        map.insert(id, value);
        Env(map)
    }
}

pub fn eval<'input, 'env>(env: &'env Env<'input>, e: Term<'input>) -> Result<Value<'input>, Error> {
    Ok(match e {
        Term::Number(n) => Value::Number(n),
        Term::Var(id) => env.lookup(&id).ok_or(Error::UnknownVar)?,
        Term::App(a, b) => {
            if let Value::Lambda(env2, x, e) = eval(env, *a)? {
                eval(&env2.insert(x, eval(env, *b)?), e)?
            } else {
                return Err(Error::AppNotFun);
            }
        }
        Term::Abs(x, e) => Value::Lambda(env.clone(), x, *e),

        _ => todo!(),
    })
}

mod tests {
    use super::*;

    #[test]
    fn test_eval_int_literal() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(eval(&Env::new(), Term::Number(42))?, Value::Number(42));
        Ok(())
    }

    #[test]
    fn test_apply_id() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            eval(
                &Env::new(),
                Term::App(
                    Box::new(Term::Abs("x", Box::new(Term::Var("x")))),
                    Box::new(Term::Number(4))
                )
            )?,
            Value::Number(4)
        );
        Ok(())
    }
}
