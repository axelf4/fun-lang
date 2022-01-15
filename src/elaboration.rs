/// Takes raw syntax and outputs core syntax.
use crate::ast as raw;
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::ops;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Icitness {
    Explicit,
    // Implicit,
}
use Icitness::*;

/// De Bruijn index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Ix(usize);
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bd {
    Bound,
    Defined,
}

/// Core term.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    /// A local variable.
    LocalVar(Ix),
    App(Box<Term>, Box<Term>),
    Abs(Box<Term>),
    /// The universe.
    Type,
    Pi(String, Box<Type>, Box<Type>),
    Meta(MetaVar),
    /// Representation of a hole plugged with a meta.
    InsertedMeta(MetaVar, Vec<Bd>),
}

type Type = Term;

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
            Term::App(t, u) => t.eval(meta_ctx, env).apply(meta_ctx, u.eval(meta_ctx, env)),
            Term::Abs(t) => Value::Abs(Closure(env.clone(), t.as_ref().clone())),
            Term::Pi(x, a, b) => Value::Pi(
                x.clone(),
                Box::new(a.eval(meta_ctx, env)),
                Closure(env.clone(), b.as_ref().clone()),
            ),
            Term::Type => Value::Type,
            Term::Meta(m) => meta_ctx.meta_value(*m),
            Term::InsertedMeta(m, bds) => meta_ctx.meta_value(*m).apply_bds(meta_ctx, env, bds),
        }
    }

    /// Wrap a term in lambdas.
    fn lambdas(self, l: Lvl) -> Term {
        (0..l.0).rev().fold(self, |t, _i| Term::Abs(Box::new(t)))
    }
}

/// A list of values.
///
/// `f spine` is notation for `f` being applied to multiple values.
#[derive(Clone, Debug)]
struct Spine(Vec<(Value, Icitness)>);

impl FromIterator<(Value, Icitness)> for Spine {
    fn from_iter<I: IntoIterator<Item = (Value, Icitness)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl Spine {
    fn new() -> Self {
        Self(Vec::new())
    }
}

#[derive(Clone, Debug)]
struct Closure(Env, Term);

impl Closure {
    fn apply(&self, meta_ctx: &MetaCtx, v: Value) -> Value {
        let Closure(env, t) = self;
        let mut env = env.clone();
        env.0.push(v);
        t.eval(meta_ctx, &env)
    }
}

/// A value.
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
    /// This is a meta applied to zero or more arguments. "Flexible"
    /// because computation can progress if the meta is solved.
    Flex(MetaVar, Spine),

    Abs(Closure),
    Pi(String, Box<Vtype>, Closure),
    /// The universe.
    Type,
}

type Vtype = Value;

impl Value {
    fn apply(self, meta_ctx: &MetaCtx, v: Value) -> Value {
        match self {
            Value::Abs(t) => t.apply(meta_ctx, v),
            // Add the argument to spines
            Value::Rigid(x, mut spine) => {
                spine.0.push((v, Explicit));
                Value::Rigid(x, spine)
            }
            Value::Flex(m, mut spine) => {
                spine.0.push((v, Explicit));
                Value::Flex(m, spine)
            }
            _ => unreachable!(),
        }
    }

    fn apply_spine(self, meta_ctx: &MetaCtx, spine: Spine) -> Value {
        spine
            .0
            .into_iter()
            .fold(self, |acc, (v, _)| acc.apply(meta_ctx, v))
    }

    /// We apply a value to a mask of entries from the environment.
    fn apply_bds(self, meta_ctx: &MetaCtx, env: &Env, bds: &[Bd]) -> Value {
        env.0.iter().zip(bds).fold(self, |acc, x| match x {
            (t, Bd::Bound) => acc.apply(meta_ctx, t.clone()),
            (_t, Bd::Defined) => acc,
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TypeError {
    // Mismatch(Term, Term),
    NotInScope(String),
    UnificationFailure,
}

impl fmt::Display for TypeError {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use TypeError::*;
        match self {
            // Mismatch(a, b) => write!(fmt, "The types {:?} and {:?} do not match.", a, b),
            NotInScope(x) => write!(fmt, "Could not find variable {}.", x),
            x => write!(fmt, "Type error: {:?}", x),
        }
    }
}

impl error::Error for TypeError {}

// /// Pair of unforced type and forced type.
// struct Gty(Value, Value);

#[derive(Clone, Debug)]
enum SymbolValue {
    // Top,
    Local(Lvl, Vtype),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct MetaVar(usize);

impl fmt::Display for MetaVar {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "?{}", self.0)
    }
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
    bds: Vec<Bd>,

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
        spine.0.into_iter().fold(t, |acc, (v, _)| {
            Term::App(Box::new(acc), Box::new(self.quote(l, v)))
        })
    }

    fn quote(&self, l: Lvl, v: Value) -> Term {
        match self.force(v) {
            Value::Flex(m, spine) => self.quote_spine(l, Term::Meta(m), spine),
            Value::Rigid(x, spine) => self.quote_spine(l, Term::LocalVar(x.to_ix(l)), spine),
            Value::Abs(t) => Term::Abs(Box::new(self.quote(
                l.inc(),
                t.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ))),
            Value::Pi(x, a, b) => Term::Pi(
                x,
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
    fn rename(&self, m: MetaVar, renaming: &PartialRenaming, v: Value) -> Result<Term, TypeError> {
        Ok(match self.force(v) {
            Value::Flex(m2, _) if m == m2 => return Err(TypeError::UnificationFailure),
            Value::Flex(m2, spine) => {
                spine.0.into_iter().try_fold(Term::Meta(m2), |t, (u, _)| {
                    Ok(Term::App(
                        Box::new(t),
                        Box::new(self.rename(m, renaming, u)?),
                    ))
                })?
            }

            Value::Rigid(x, spine) => {
                let x2 = *renaming.map.get(&x).ok_or(TypeError::UnificationFailure)?;
                spine.0.into_iter().try_fold(
                    Term::LocalVar(x2.to_ix(Lvl(renaming.dom))),
                    |t, (u, _)| {
                        Ok(Term::App(
                            Box::new(t),
                            Box::new(self.rename(m, renaming, u)?),
                        ))
                    },
                )?
            }

            Value::Abs(t) => Term::Abs(Box::new(self.rename(
                m,
                &renaming.clone().lift(),
                t.apply(
                    &self.meta_ctx,
                    Value::Rigid(Lvl(renaming.cod), Spine::new()),
                ),
            )?)),

            Value::Pi(x, a, b) => Term::Pi(
                x,
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
    fn solve(&mut self, gamma: Lvl, m: MetaVar, spine: Spine, rhs: Value) -> Result<(), TypeError> {
        let renaming = self
            .invert(gamma, spine)
            .ok_or(TypeError::UnificationFailure)?;
        let rhs = self.rename(m, &renaming, rhs)?;
        let solution = rhs
            .lambdas(Lvl(renaming.dom))
            .eval(&self.meta_ctx, &Env::new());
        self.meta_ctx.0[m.0] = MetaEntry::Solved(solution);
        Ok(())
    }

    fn unify_spine(&mut self, l: Lvl, s1: Spine, s2: Spine) -> Result<(), TypeError> {
        if s1.0.len() != s2.0.len() {
            return Err(TypeError::UnificationFailure); // rigid mismatch error
        }
        s1.0.into_iter()
            .zip(s2.0)
            .try_for_each(|((v1, _), (v2, _))| self.unify(l, v1, v2))
    }

    fn unify(&mut self, l: Lvl, v1: Value, v2: Value) -> Result<(), TypeError> {
        let x = match (self.force(v1), self.force(v2)) {
            (Value::Abs(t1), Value::Abs(t2)) => self.unify(
                l.inc(),
                t1.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                t2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ),
            (t1, Value::Abs(t2)) => self.unify(
                l.inc(),
                t1.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                t2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ),
            (Value::Abs(t1), t2) => self.unify(
                l.inc(),
                t1.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
                t2.apply(&self.meta_ctx, Value::Rigid(l, Spine::new())),
            ),
            (Value::Type, Value::Type) => Ok(()),

            (Value::Rigid(x1, sp1), Value::Rigid(x2, sp2)) if x1 == x2 => {
                self.unify_spine(l, sp1, sp2)
            }
            (Value::Flex(m1, sp1), Value::Flex(m2, sp2)) if m1 == m2 => {
                self.unify_spine(l, sp1, sp2)
            }

            (Value::Flex(m, sp), v) => self.solve(l, m, sp, v),
            (v, Value::Flex(m, sp)) => self.solve(l, m, sp, v),
            _ => Err(TypeError::UnificationFailure), // rigid mismatch error
        };
        x
    }

    /// Run the function in this context extended with a bound
    /// variable/definition.
    fn with<R, F: FnOnce(&mut Ctx<'input>) -> R>(
        &mut self,
        x: &'input str,
        a: Vtype,
        bd: Bd,
        f: F,
    ) -> R {
        let l = self.lvl();
        self.env.0.push(Value::Rigid(l, Spine::new()));
        self.bds.push(bd);
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

    fn infer(&mut self, term: &raw::Term<'input>) -> Result<(Term, Vtype), TypeError> {
        Ok(match term {
            raw::Term::Var(x) => {
                match self
                    .table
                    .get(x)
                    .ok_or_else(|| TypeError::NotInScope(x.to_string()))?
                {
                    SymbolValue::Local(x, a) => (Term::LocalVar(x.to_ix(self.lvl())), a.clone()),
                }
            }

            raw::Term::Abs(x, t) => {
                // Find out the argument type. If no annotation:
                // Create a new meta.
                let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                let (t, b) = self.with(x, a.clone(), Bd::Bound, |ctx| ctx.infer(t.as_ref()))?;
                (
                    Term::Abs(Box::new(t)),
                    Value::Pi(x.to_string(), Box::new(a), self.close_value(b)),
                )
            }

            raw::Term::App(t, u) => {
                let (t, tty) = self.infer(t)?;
                // Ensure that tty is Pi
                let (a, b) = match self.force(tty) {
                    Value::Pi(_x, a, b) => (*a, b),
                    tty => {
                        let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                        let b = Closure(
                            self.env.clone(),
                            self.with("x", a.clone(), Bd::Bound, |ctx| ctx.fresh_meta()),
                        );
                        self.unify(
                            self.lvl(),
                            tty,
                            Value::Pi("x".to_string(), Box::new(a.clone()), b.clone()),
                        )?;
                        (a, b)
                    }
                };
                let u = self.check(u, a)?;
                let v = b.apply(&self.meta_ctx, u.eval(&self.meta_ctx, &self.env));
                (Term::App(Box::new(t), Box::new(u)), v)
            }

            raw::Term::Type => (Term::Type, Value::Type),

            raw::Term::Pi(x, a, b) => {
                let a = self.check(a.as_ref(), Value::Type)?;
                let b = self.with(x, a.eval(&self.meta_ctx, &self.env), Bd::Bound, |ctx| {
                    ctx.check(b.as_ref(), Value::Type)
                })?;
                (
                    Term::Pi(x.to_string(), Box::new(a), Box::new(b)),
                    Value::Type,
                )
            }

            raw::Term::Hole => {
                let t = self.fresh_meta();
                let a = self.fresh_meta().eval(&self.meta_ctx, &self.env);
                (t, a)
            }

            raw::Term::Number(_) => todo!(),
        })
    }

    fn check(&mut self, t: &raw::Term<'input>, a: Vtype) -> Result<Term, TypeError> {
        Ok(match (t, self.force(a)) {
            (raw::Term::Abs(x, t), Value::Pi(_, a, b)) => {
                let l = self.lvl();
                Term::Abs(Box::new(self.with(x, *a, Bd::Bound, |ctx| {
                    let x = ctx.check(
                        t.as_ref(),
                        b.apply(&ctx.meta_ctx, Value::Rigid(l, Spine::new())),
                    );
                    x
                })?))
            }

            (raw::Term::Hole, _) => self.fresh_meta(),

            (t, expected) => {
                let (t, inferred) = self.infer(t)?;
                self.unify(self.lvl(), expected, inferred)?;
                t
            }
        })
    }
}

pub fn elaborate<'input>(t: &raw::Term<'input>) -> Result<(Term, Term), TypeError> {
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
                Term::Abs(Box::new(Term::LocalVar(Ix(0)))),
                Term::Pi(
                    "x".to_string(),
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
                Term::Pi("x".to_string(), Box::new(Term::Type), Box::new(Term::Type)),
                Term::Type
            )
        );
        Ok(())
    }
}
