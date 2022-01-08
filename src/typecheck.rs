use crate::ast::Expr;
use hashbrown::HashMap;
use std::collections::VecDeque;
use std::fmt;
use std::mem;

type TypeVar = usize;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type {
    Number,
    Var(TypeVar),
    Fun(Box<(Type, Type)>),
}

impl fmt::Display for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Number => write!(fmt, "Num"),
            Type::Var(_i) => write!(fmt, "X"), // TODO
            Type::Fun(x) => write!(fmt, "{} → {}", x.0, x.1),
        }
    }
}

impl Type {
    fn contains(&self, v: TypeVar) -> bool {
        match self {
            Type::Number => false,
            Type::Var(u) => v == *u,
            Type::Fun(f) => f.0.contains(v) || f.1.contains(v),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum Error {
    UnknownVar,
    AppNonFun,
    InfiniteType,
    UnificationFailure,
}

struct Constraint(Type, Type);

struct State {
    next_var: usize,
    constraints: Vec<Constraint>,
}

impl State {
    fn new() -> Self {
        Self {
            next_var: 0,
            constraints: Vec::new(),
        }
    }

    fn new_type_var(&mut self) -> Type {
        let ty = Type::Var(self.next_var);
        self.next_var += 1;
        ty
    }

    fn equate(&mut self, ty1: Type, ty2: Type) {
        self.constraints.push(Constraint(ty1, ty2));
    }
}

struct Ctx<'a>(HashMap<&'a str, Type>);

impl<'a> Ctx<'a> {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn lookup(&self, id: &str) -> Option<Type> {
        self.0.get(id).cloned()
    }

    fn insert(&self, id: &'a str, ty: Type) -> Ctx<'a> {
        let mut map = self.0.clone();
        map.insert(id, ty);
        Ctx(map)
    }
}

fn infer<'a, 'ctx>(state: &mut State, ctx: &'ctx Ctx, e: Expr<'a>) -> Result<Type, Error> {
    Ok(match e {
        Expr::Number(_) => Type::Number,
        Expr::Var(id) => ctx.lookup(id).ok_or(Error::UnknownVar)?,
        Expr::Abs(x, e) => {
            let s = state.new_type_var();
            let t = infer(state, &ctx.insert(x, s.clone()), *e)?;
            Type::Fun(Box::new((s, t)))
        }
        Expr::App(f, e) => {
            // Can be simplified
            let r = infer(state, ctx, *f)?;
            let s = infer(state, ctx, *e)?;
            match r {
                Type::Fun(x) => {
                    let (s2, t) = *x;
                    state.equate(s, s2);
                    t
                }
                v @ Type::Var(_) => {
                    let t = state.new_type_var();
                    state.equate(v, Type::Fun(Box::new((s, t.clone()))));
                    t
                }
                _ => return Err(Error::AppNonFun),
            }
        }
    })
}

/// A substitution `{t₁/v₁, ..., tₙ/vₙ}`.
///
/// All `v`:s must be mutually unique.
#[derive(Clone, Debug)]
struct Substitution(HashMap<TypeVar, Type>);

impl Substitution {
    fn new() -> Self {
        Self(HashMap::new())
    }

    /// Returns a singleton substitution `{t/v}`.
    ///
    /// The variable `v` may not occur in the replacement term `t`.
    fn single(v: TypeVar, t: Type) -> Option<Self> {
        if t.contains(v) {
            None
        } else {
            Some(Self([(v, t)].into_iter().collect()))
        }
    }

    /// Performs the specified substitution on the given expression (`eθ`).
    ///
    /// Returns the new expression obtained by simultaneously replacing
    /// each occurence of the free substituted variables by their
    /// respective replacements.
    fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Number => Type::Number,
            Type::Var(v) => self.0.get(&v).cloned().unwrap_or_else(|| ty.clone()),
            Type::Fun(f) => Type::Fun(Box::new((self.apply(&f.0), self.apply(&f.1)))),
        }
    }

    /// Returns the composition of the two substitutions.
    fn compose(mut a: Self, b: Self) -> Self {
        mem::drop(a.0.drain_filter(|&v, t| {
            *t = b.apply(t);
            *t == Type::Var(v) // Remove if null-op
        }));
        a.0.extend(b.0);
        a
    }
}

impl fmt::Display for Substitution {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{{")?;
        let mut first = true;
        self.0.iter().try_for_each::<_, fmt::Result>(|(v, t)| {
            write!(fmt, "{}/{}", t, v)?;
            if !first {
                write!(fmt, ", ")?;
            }
            first = false;
            Ok(())
        })?;
        write!(fmt, "}}")
    }
}

fn unify(constraints: Vec<Constraint>) -> Result<Substitution, Error> {
    let mut sub = Substitution::new();
    let mut constraints: VecDeque<_> = constraints.into();

    while let Some(Constraint(ty1, ty2)) = constraints.pop_front() {
        match (sub.apply(&ty1), sub.apply(&ty2)) {
            (Type::Number, Type::Number) => {}
            (Type::Var(x1), Type::Var(x2)) if x1 == x2 => {}

            (Type::Fun(x1), Type::Fun(x2)) => {
                let (s1, t1) = *x1;
                let (s2, t2) = *x2;
                constraints.push_back(Constraint(s1, s2));
                constraints.push_back(Constraint(t1, t2));
            }

            (Type::Var(v), t) => {
                sub = Substitution::compose(
                    sub.clone(),
                    Substitution::single(v, t).ok_or(Error::InfiniteType)?,
                );
            }
            (t, Type::Var(v)) => {
                sub = Substitution::compose(
                    sub.clone(),
                    Substitution::single(v, t).ok_or(Error::InfiniteType)?,
                );
            }

            (_, _) => return Err(Error::UnificationFailure),
        }
    }

    Ok(sub)
}

pub fn typecheck<'a>(e: Expr<'a>) -> Result<Type, Error> {
    let mut state = State::new();
    let ty = infer(&mut state, &Ctx::new(), e)?;
    let sub = unify(state.constraints)?;
    Ok(sub.apply(&ty))
}

mod tests {
    use super::*;

    #[test]
    fn test_simple_literal() {
        assert_eq!(typecheck(Expr::Number(0)), Ok(Type::Number));
    }

    /// Try to compute the type of "λ x → x x".
    #[test]
    fn test_occurs_check() {
        assert_eq!(
            typecheck(Expr::Abs(
                "x",
                Box::new(Expr::App(
                    Box::new(Expr::Var("x")),
                    Box::new(Expr::Var("x"))
                ))
            )),
            Err(Error::InfiniteType)
        );
    }
}
