/// Takes raw syntax and outputs core syntax.
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::ops;

use crate::ast as raw;
use crate::core::{
    Icitness::{self, *},
    Ix, MetaVar, Term, Type,
};

/// De Bruijn level.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Lvl(usize);

impl Lvl {
    fn to_ix(self, Lvl(count): Lvl) -> Ix {
        Ix(count - 1 - self.0)
    }

    fn inc(self) -> Self {
        Self(self.0 + 1)
    }
}

#[derive(Clone, Default, Debug)]
struct Env(Vec<Value>);

impl Env {
    fn new() -> Self {
        Self(Vec::new())
    }
}

impl ops::Index<Ix> for Env {
    type Output = Value;
    fn index(&self, index: Ix) -> &Self::Output {
        &self.0[self.0.len() - 1 - index.0]
    }
}

impl Term {
    fn eval(&self, meta_ctx: &MetaCtx, env: &Env) -> Value {
        match self {
            Term::LocalVar(x) => env[*x].clone(),
            Term::App(t, i, u) => t
                .eval(meta_ctx, env)
                .apply(meta_ctx, *i, u.eval(meta_ctx, env)),
            Term::Abs(i, t) => Value::Abs(*i, Closure(env.clone(), t.as_ref().clone())),
            Term::Pi(i, a, b) => Value::Pi(
                *i,
                Box::new(a.eval(meta_ctx, env)),
                Closure(env.clone(), b.as_ref().clone()),
            ),
            Term::Type => Value::Type,
            Term::Meta(m) => meta_ctx.meta_value(*m),
            Term::InsertedMeta(m, bds) => meta_ctx.meta_value(*m).apply_bds(meta_ctx, env, bds),
        }
    }
}

/// A list of values.
///
/// `f spine` is notation for `f` being applied to multiple values.
#[derive(Clone, Debug)]
struct Spine(Vec<(Value, Icitness)>);

impl Spine {
    fn new() -> Self {
        Self(Vec::new())
    }
}

impl FromIterator<(Value, Icitness)> for Spine {
    fn from_iter<I: IntoIterator<Item = (Value, Icitness)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[derive(Clone, Debug)]
struct Closure(Env, Term);

impl Closure {
    fn apply(self, meta_ctx: &MetaCtx, v: Value) -> Value {
        let Closure(mut env, t) = self;
        env.0.push(v);
        t.eval(meta_ctx, &env)
    }
}

/// Semantic value.
///
/// Computation can block on metas or variables, giving neutral
/// values.
#[derive(Clone, Debug)]
enum Value {
    /// Rigid neutral value.
    ///
    /// This is a bound variable applied to zero or more arguments.
    Rigid(Lvl, Spine),
    /// Flexible neutral value.
    ///
    /// This is a meta applied to zero or more arguments.
    Flex(MetaVar, Spine),

    Abs(Icitness, Closure),
    Pi(Icitness, Box<Vtype>, Closure),
    /// The universe.
    Type,
}

type Vtype = Value;

impl Value {
    fn apply(self, meta_ctx: &MetaCtx, i: Icitness, v: Value) -> Value {
        match self {
            Value::Abs(_, t) => t.apply(meta_ctx, v),
            // Append the argument to spines
            Value::Rigid(x, mut spine) => {
                spine.0.push((v, i));
                Value::Rigid(x, spine)
            }
            Value::Flex(m, mut spine) => {
                spine.0.push((v, i));
                Value::Flex(m, spine)
            }
            _ => unreachable!(),
        }
    }

    fn apply_spine(self, meta_ctx: &MetaCtx, spine: Spine) -> Value {
        spine
            .0
            .into_iter()
            .fold(self, |acc, (v, i)| acc.apply(meta_ctx, i, v))
    }

    /// We apply a value to a mask of entries from the environment.
    fn apply_bds(self, meta_ctx: &MetaCtx, env: &Env, bds: &[bool]) -> Value {
        env.0
            .iter()
            .zip(bds)
            .filter(|(_, &x)| x)
            .fold(self, |acc, (t, _)| acc.apply(meta_ctx, Explicit, t.clone()))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    // Mismatch(Term, Term),
    NotInScope(String),
    UnificationFailure,
    IcitnessMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            // Mismatch(a, b) => write!(fmt, "The types {:?} and {:?} do not match.", a, b),
            NotInScope(x) => write!(fmt, "Could not find variable {}.", x),
            IcitnessMismatch => write!(
                fmt,
                "found explicit/implicit argument when the other was expected"
            ),
            x => write!(fmt, "Type error: {:?}", x),
        }
    }
}

impl error::Error for Error {}

// /// Pair of unforced value and forced value.
// struct Glued(Value, Value);

#[derive(Clone, Debug)]
enum SymbolValue {
    // Top,
    Local(Lvl, Vtype),
}

#[derive(Clone, Debug)]
enum MetaEntry {
    Unsolved,
    Solved(Value),
}

/// Conceptually a bunch of mutually recursive definitions that live in
/// the topmost scope. Each metavariable may or may not have such a
/// definition.
///
/// Metavariables may be solved during unification.
#[derive(Debug)]
struct MetaCtx(Vec<MetaEntry>);

impl MetaCtx {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn fresh(&mut self) -> MetaVar {
        let x = self.0.len();
        self.0.push(MetaEntry::Unsolved);
        MetaVar(x)
    }

    fn meta_value(&self, m: MetaVar) -> Value {
        match &self[m] {
            MetaEntry::Solved(v) => v.clone(),
            MetaEntry::Unsolved => Value::Flex(m, Spine::new()),
        }
    }
}

impl ops::Index<MetaVar> for MetaCtx {
    type Output = MetaEntry;
    fn index(&self, index: MetaVar) -> &Self::Output {
        &self.0[index.0]
    }
}

/// Partial renaming from `Γ` to `Δ`.
#[derive(Clone, Default, Debug)]
struct PartialRenaming {
    /// Size of Γ.
    dom: usize,
    /// Size of Δ.
    cod: usize,
    /// Mapping from Δ vars to Γ vars.
    map: HashMap<Lvl, Lvl>,
}

impl PartialRenaming {
    /// Lift over an extra bound variable.
    fn lift(self) -> Self {
        let mut map = self.map;
        map.insert(Lvl(self.cod), Lvl(self.dom));
        Self {
            dom: self.dom + 1,
            cod: self.cod + 1,
            map,
        }
    }
}

impl fmt::Display for PartialRenaming {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "[")?;
        let mut first = true;
        self.map.iter().try_for_each(|(Lvl(x), Lvl(y))| {
            if !first {
                write!(fmt, ", ")?;
            }
            first = false;
            write!(fmt, "{} ↦ {}", x, y)
        })?;
        write!(fmt, "]")
    }
}

#[derive(Debug)]
struct Ctx<'input> {
    meta_ctx: MetaCtx,

    /// Local evaluation environment.
    env: Env,
    /// Mask of what entries in the local context metas abstract over.
    bds: Vec<bool>,

    /// Symbol table.
    table: HashMap<&'input str, SymbolValue>,
}

impl<'input> Ctx<'input> {
    fn new() -> Self {
        Self {
            meta_ctx: MetaCtx::new(),
            env: Env::new(),
            bds: Vec::new(),
            table: HashMap::new(),
        }
    }

    /// Returns the size of the local context.
    fn lvl(&self) -> Lvl {
        Lvl(self.env.0.len())
    }

    fn fresh_meta(&mut self) -> Term {
        let meta_var = self.meta_ctx.fresh();
        let t = Term::InsertedMeta(meta_var, self.bds.clone());
        // Contextual metavariables means creating a function that
        // abstracts over the bound variables in scope.
        t
    }

    fn force(&self, v: Value) -> Value {
        match v {
            Value::Flex(m, spine) => {
                if let MetaEntry::Solved(v) = &self.meta_ctx[m] {
                    let v = v.clone();
                    self.force(v.apply_spine(&self.meta_ctx, spine))
                } else {
                    Value::Flex(m, spine)
                }
            }
            v => v,
        }
    }

    fn quote_spine(&self, l: Lvl, t: Term, spine: Spine) -> Term {
        spine.0.into_iter().fold(t, |acc, (v, i)| {
            Term::App(Box::new(acc), i, Box::new(self.quote(l, v)))
        })
    }

    fn quote(&self, l: Lvl, v: Value) -> Term {
        match self.force(v) {
            Value::Flex(m, spine) => self.quote_spine(l, Term::Meta(m), spine),
            Value::Rigid(x, spine) => self.quote_spine(l, Term::LocalVar(x.to_ix(l)), spine),
            Value::Abs(i, t) => Term::Abs(
                i,
                Box::new(self.quote(
                    l.inc(),
                    t.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                )),
            ),
            Value::Pi(i, a, b) => Term::Pi(
                i,
                Box::new(self.quote(l, *a)),
                Box::new(self.quote(
                    l.inc(),
                    b.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                )),
            ),
            Value::Type => Term::Type,
        }
    }

    /// The normalization function.
    #[allow(unused)]
    fn nf(&mut self, t: Term) -> Term {
        let v = t.eval(&self.meta_ctx, &self.env);
        self.quote(self.lvl(), v)
    }

    fn invert(&self, gamma: Lvl, spine: Spine) -> Option<PartialRenaming> {
        let dom = spine.0.len();
        let renaming = spine.0.into_iter().enumerate().try_fold(
            HashMap::new(),
            |mut renaming, (y, (v, _))| match self.force(v) {
                Value::Rigid(x, spine) if spine.0.is_empty() => {
                    renaming.insert(x, Lvl(y));
                    Some(renaming)
                }
                _ => None,
            },
        )?;
        Some(PartialRenaming {
            dom,
            cod: gamma.0,
            map: renaming,
        })
    }

    /// Perform the renaming on rhs, while checking for `m` occurrences.
    fn rename(&self, m: MetaVar, renaming: &PartialRenaming, v: Value) -> Result<Term, Error> {
        let go_spine = |t, spine: Spine| {
            spine.0.into_iter().try_fold(t, |t, (u, i)| {
                Ok(Term::App(
                    Box::new(t),
                    i,
                    Box::new(self.rename(m, renaming, u)?),
                ))
            })
        };

        Ok(match self.force(v) {
            Value::Flex(m2, _) if m == m2 => return Err(Error::UnificationFailure),
            Value::Flex(m2, spine) => go_spine(Term::Meta(m2), spine)?,

            Value::Rigid(x, spine) => {
                let x2 = *renaming.map.get(&x).ok_or(Error::UnificationFailure)?;
                go_spine(Term::LocalVar(x2.to_ix(Lvl(renaming.dom))), spine)?
            }

            Value::Abs(i, t) => Term::Abs(
                i,
                Box::new(self.rename(
                    m,
                    &renaming.clone().lift(),
                    t.apply(
                        &self.meta_ctx,
                        Value::Rigid(Lvl(renaming.cod), Spine::new()),
                    ),
                )?),
            ),

            Value::Pi(i, a, b) => Term::Pi(
                i,
                Box::new(self.rename(m, renaming, *a)?),
                Box::new(self.rename(
                    m,
                    &renaming.clone().lift(),
                    b.apply(
                        &self.meta_ctx,
                        Value::Rigid(Lvl(renaming.cod), Spine::new()),
                    ),
                )?),
            ),

            Value::Type => Term::Type,
        })
    }

    /// Solve the problem:
    ///
    ///    ?α spine =? rhs
    fn solve(&mut self, gamma: Lvl, m: MetaVar, spine: Spine, rhs: Value) -> Result<(), Error> {
        let is: Vec<_> = spine.0.iter().map(|(_, i)| *i).collect();
        let renaming = self.invert(gamma, spine).ok_or(Error::UnificationFailure)?;
        let rhs = self.rename(m, &renaming, rhs)?;
        let solution = is
            .into_iter()
            .rev()
            .fold(rhs, |t, i| Term::Abs(i, Box::new(t)))
            .eval(&self.meta_ctx, &Env::new());
        self.meta_ctx.0[m.0] = MetaEntry::Solved(solution);
        Ok(())
    }

    fn unify_spine(&mut self, l: Lvl, s1: Spine, s2: Spine) -> Result<(), Error> {
        if s1.0.len() != s2.0.len() {
            return Err(Error::UnificationFailure); // rigid mismatch error
        }
        s1.0.into_iter()
            .zip(s2.0)
            .try_for_each(|((v1, _), (v2, _))| self.unify(l, v1, v2))
    }

    fn unify(&mut self, l: Lvl, v1: Value, v2: Value) -> Result<(), Error> {
        let x = match (self.force(v1), self.force(v2)) {
            (Value::Abs(_, t1), Value::Abs(_, t2)) => self.unify(
                l.inc(),
                t1.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                t2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ),
            (t1, Value::Abs(i, t2)) | (Value::Abs(i, t2), t1) => self.unify(
                l.inc(),
                t1.apply(&self.meta_ctx, i, Value::Rigid(l, Spine::new())),
                t2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ),
            (Value::Type, Value::Type) => Ok(()),
            (Value::Pi(i1, a1, b1), Value::Pi(i2, a2, b2)) if i1 == i2 => {
                self.unify(l, *a1, *a2)?;
                self.unify(
                    l.inc(),
                    b1.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                    b2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                )
            }

            (Value::Rigid(x1, sp1), Value::Rigid(x2, sp2)) if x1 == x2 => {
                self.unify_spine(l, sp1, sp2)
            }
            (Value::Flex(m1, sp1), Value::Flex(m2, sp2)) if m1 == m2 => {
                self.unify_spine(l, sp1, sp2)
            }

            (Value::Flex(m, sp), v) | (v, Value::Flex(m, sp)) => self.solve(l, m, sp, v),
            _ => Err(Error::UnificationFailure), // rigid mismatch error
        };
        x
    }

    /// Run the function in this context extended with a bound
    /// variable/definition (TODO).
    fn with<R>(&mut self, x: &'input str, a: Vtype, f: impl FnOnce(&mut Ctx<'input>) -> R) -> R {
        let l = self.lvl();
        self.env.0.push(Value::Rigid(l, Spine::new()));
        self.bds.push(true);
        let old_sym = self.table.insert(x, SymbolValue::Local(l, a));

        let result = f(self);

        if let Some(sym) = old_sym {
            self.table.insert(x, sym);
        } else {
            self.table.remove(x);
        }
        self.bds.pop();
        self.env.0.pop();

        result
    }

    fn close_value(&mut self, v: Value) -> Closure {
        Closure(self.env.clone(), self.quote(self.lvl().inc(), v))
    }

    /// Insert fresh implicit applications.
    fn insert_implicits(&mut self, mut t: Term, mut va: Vtype) -> (Term, Vtype) {
        loop {
            match self.force(va) {
                Value::Pi(Implicit, _a, b) => {
                    let m = self.fresh_meta();
                    t = Term::App(Box::new(t), Implicit, Box::new(m.clone()));
                    va = b.apply(&self.meta_ctx, m.eval(&self.meta_ctx, &self.env));
                }
                va => break (t, va),
            }
        }
    }

    fn infer(&mut self, term: &raw::Term<'input>) -> Result<(Term, Vtype), Error> {
        Ok(match term {
            raw::Term::Var(x) => {
                match self
                    .table
                    .get(x)
                    .ok_or_else(|| Error::NotInScope(x.to_string()))?
                {
                    SymbolValue::Local(x, a) => (Term::LocalVar(x.to_ix(self.lvl())), a.clone()),
                }
            }

            raw::Term::Abs(i, x, t) => {
                let i = *i;
                let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                let (t, b) = match self.with(x, a.clone(), |ctx| ctx.infer(t.as_ref()))? {
                    x @ (Type::Abs(Implicit, _), _) => x,
                    // Insert fresh implicit applications to a term
                    // which is not an implicit lambda (i.e. neutral).
                    (t, b) => self.insert_implicits(t, b),
                };
                (
                    Term::Abs(i, Box::new(t)),
                    Value::Pi(i, Box::new(a), self.close_value(b)),
                )
            }

            raw::Term::App(t, i, u) => {
                let i = *i;
                let (t, tty) = match (i, self.infer(t)?) {
                    (Implicit, x) => x,
                    (Explicit, (t, tty)) => self.insert_implicits(t, tty),
                };
                // Ensure that tty is Pi
                let (a, b) = match self.force(tty) {
                    Value::Pi(i2, _a, _b) if i != i2 => return Err(Error::IcitnessMismatch),
                    Value::Pi(_i2, a, b) => (*a, b),
                    tty => {
                        let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                        let b = Closure(
                            self.env.clone(),
                            self.with("x", a.clone(), |ctx| ctx.fresh_meta()),
                        );
                        self.unify(
                            self.lvl(),
                            tty,
                            Value::Pi(i, Box::new(a.clone()), b.clone()),
                        )?;
                        (a, b)
                    }
                };
                let u = self.check(u, a)?;
                let v = b.apply(&self.meta_ctx, u.eval(&self.meta_ctx, &self.env));
                (Term::App(Box::new(t), i, Box::new(u)), v)
            }

            raw::Term::Type => (Term::Type, Value::Type),

            raw::Term::Pi(x, a, b) => {
                let a = self.check(a.as_ref(), Value::Type)?;
                let b = self.with(x, a.eval(&self.meta_ctx, &self.env), |ctx| {
                    ctx.check(b.as_ref(), Value::Type)
                })?;
                (Term::Pi(Explicit, Box::new(a), Box::new(b)), Value::Type)
            }

            raw::Term::Hole => {
                let t = self.fresh_meta();
                let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                (t, a)
            }

            raw::Term::Number(_) => todo!(),
        })
    }

    fn check(&mut self, t: &raw::Term<'input>, a: Vtype) -> Result<Term, Error> {
        Ok(match (t, self.force(a)) {
            (raw::Term::Abs(i2, x, t), Value::Pi(i, a, b)) if i == *i2 => {
                let l = self.lvl();
                Term::Abs(
                    i,
                    Box::new(self.with(x, *a, |ctx| {
                        let x = ctx.check(
                            t.as_ref(),
                            b.apply(&ctx.meta_ctx, Value::Rigid(l, Spine::new())),
                        );
                        x
                    })?),
                )
            }
            // TODO If Pi is implicit insert a new implicit lambda
            (raw::Term::Hole, _) => self.fresh_meta(),

            (t, expected) => {
                let (t, inferred) = self.infer(t)?;
                self.unify(self.lvl(), expected, inferred)?;
                t
            }
        })
    }
}

pub fn elaborate<'input>(t: &raw::Term<'input>) -> Result<(Term, Term), Error> {
    let mut ctx = Ctx::new();
    let (t, vty) = ctx.infer(t)?;
    Ok((t, ctx.quote(ctx.lvl(), vty)))
}

mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::parse;

    #[test]
    fn test_elaborate_id() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            elaborate(&parse(Lexer::new(r"\x -> x"))?)?,
            (
                Term::Abs(Explicit, Box::new(Term::LocalVar(Ix(0)))),
                Term::Pi(
                    Explicit,
                    Box::new(Term::Meta(MetaVar(0))),
                    Box::new(Term::Meta(MetaVar(0)))
                )
            )
        );
        Ok(())
    }

    #[test]
    fn test_elaborate_simple_pi() -> Result<(), Box<dyn error::Error>> {
        assert_eq!(
            elaborate(&parse(Lexer::new("(x : Type) -> Type"))?)?,
            (
                Term::Pi(Explicit, Box::new(Term::Type), Box::new(Term::Type)),
                Term::Type
            )
        );
        Ok(())
    }

    /// Try to compute the type of "λ x → x x".
    #[test]
    fn test_occurs_check() {
        assert_eq!(
            elaborate(&raw::Term::Abs(
                Explicit,
                "x",
                Box::new(raw::Term::App(
                    Box::new(raw::Term::Var("x")),
                    Explicit,
                    Box::new(raw::Term::Var("x"))
                ))
            )),
            Err(Error::UnificationFailure)
        );
    }
}
