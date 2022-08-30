/// Takes raw syntax and outputs core syntax.
use std::collections::HashMap;
use std::error;
use std::fmt;
use std::ops;

use crate::ast as raw;
use crate::ast::Id;
use crate::core::{
    Definition,
    Icitness::{self, *},
    Idx, MetaVar, Term, Type,
};

/// De Bruijn level.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Lvl(usize);

impl Lvl {
    fn to_idx(self, Lvl(count): Lvl) -> Idx {
        Idx(count - 1 - self.0)
    }

    fn inc(self) -> Self {
        Self(self.0 + 1)
    }
}

/// Local environment.
#[derive(Clone, Default, Debug)]
struct Env(Vec<Value>);

impl Env {
    fn new() -> Self {
        Self(Vec::new())
    }

    /// Returns the size of the local context.
    fn lvl(&self) -> Lvl {
        Lvl(self.0.len())
    }
}

impl ops::Index<Idx> for Env {
    type Output = Value;
    fn index(&self, index: Idx) -> &Self::Output {
        &self.0[self.0.len() - 1 - index.0]
    }
}

impl Term {
    fn eval(&self, g: &GlobalCtx, env: &Env) -> Value {
        match self {
            Term::Local(x) => env[*x].clone(),
            Term::Global(x) => {
                let Definition::Constant { value, .. } = elaborate(g.db, g.program.unwrap(), *x)
                    .expect("Should have already been typechecked?");
                value.eval(g, env)
            }
            Term::App(t, i, u) => t.eval(g, env).apply(g, *i, u.eval(g, env)),
            Term::Abs(i, t) => Value::Abs(*i, Closure(env.clone(), t.as_ref().clone())),
            Term::Pi(i, a, b) => Value::Pi(
                *i,
                Box::new(a.eval(g, env)),
                Closure(env.clone(), b.as_ref().clone()),
            ),
            Term::Type => Value::Type,
            Term::Meta(m) => g.meta_ctx.meta_value(*m),
            Term::InsertedMeta(m, bds) => g.meta_ctx.meta_value(*m).apply_bds(g, env, bds),
        }
    }

    /// Replace meta-variables with their solutions.
    fn zonk(&mut self, g: &GlobalCtx, env: &mut Env) -> Result<(), Error> {
        match self {
            Term::Local(_) | Term::Global(_) | Term::Type => (),
            Term::Abs(_, t) => {
                env.0.push(Value::Rigid(env.lvl(), Spine::new()));
                t.zonk(g, env)?;
                env.0.pop();
            }
            Term::App(a, _, b) => {
                a.zonk(g, env)?;
                b.zonk(g, env)?;
            }
            Term::Pi(_, a, b) => {
                a.zonk(g, env)?;
                env.0.push(Value::Rigid(env.lvl(), Spine::new()));
                b.zonk(g, env)?;
                env.0.pop();
            }
            Term::Meta(m) => {
                if let MetaEntry::Solved(v) = &g.meta_ctx[*m] {
                    *self = v.clone().quote(g, env.lvl());
                    self.zonk(g, env)?;
                } else {
                    return Err(Error::UnsolvedMeta);
                }
            }
            Term::InsertedMeta(m, bds) => {
                if let MetaEntry::Solved(v) = &g.meta_ctx[*m] {
                    *self = v.clone().apply_bds(g, env, bds).quote(g, env.lvl());
                    self.zonk(g, env)?;
                } else {
                    return Err(Error::UnsolvedMeta);
                }
            }
        }
        Ok(())
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
    fn apply(self, g: &GlobalCtx, v: Value) -> Value {
        let Closure(mut env, t) = self;
        env.0.push(v);
        t.eval(g, &env)
    }
}

/// Semantic value.
///
/// Computation can be blocked on metas or arguments, giving neutral
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
    fn apply(self, g: &GlobalCtx, i: Icitness, v: Value) -> Value {
        match self {
            Value::Abs(_, t) => t.apply(g, v),
            // Append the argument to spines
            Value::Rigid(x, mut spine) => {
                spine.0.push((v, i));
                Value::Rigid(x, spine)
            }
            Value::Flex(m, mut spine) => {
                spine.0.push((v, i));
                Value::Flex(m, spine)
            }
            _ => unreachable!("Cannot apply a non function value"),
        }
    }

    fn apply_spine(self, g: &GlobalCtx, spine: Spine) -> Value {
        spine
            .0
            .into_iter()
            .fold(self, |acc, (v, i)| acc.apply(g, i, v))
    }

    /// We apply a value to a mask of entries from the environment.
    fn apply_bds(self, g: &GlobalCtx, env: &Env, bds: &[bool]) -> Value {
        env.0
            .iter()
            .zip(bds)
            .filter(|(_, &x)| x)
            .fold(self, |acc, (t, _)| acc.apply(g, Explicit, t.clone()))
    }

    fn force(self, g: &GlobalCtx) -> Self {
        match self {
            Value::Flex(m, spine) => {
                if let MetaEntry::Solved(v) = &g.meta_ctx[m] {
                    v.clone().apply_spine(g, spine).force(g)
                } else {
                    Value::Flex(m, spine)
                }
            }
            v => v,
        }
    }

    fn quote(self, g: &GlobalCtx, l: Lvl) -> Term {
        let quote_spine = |t: Term, spine: Spine| {
            spine.0.into_iter().fold(t, |acc, (v, i)| {
                Term::App(Box::new(acc), i, Box::new(v.quote(g, l)))
            })
        };

        match self.force(g) {
            Value::Rigid(x, spine) => quote_spine(Term::Local(x.to_idx(l)), spine),
            Value::Flex(m, spine) => quote_spine(Term::Meta(m), spine),
            Value::Abs(i, t) => Term::Abs(
                i,
                Box::new(t.apply(g, Value::Rigid(l, Spine::new())).quote(g, l.inc())),
            ),
            Value::Pi(i, a, b) => Term::Pi(
                i,
                Box::new(a.quote(g, l)),
                Box::new(b.apply(g, Value::Rigid(l, Spine::new())).quote(g, l.inc())),
            ),
            Value::Type => Term::Type,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    // Mismatch(Term, Term),
    NotInScope(String),
    UnificationFailure,
    IcitnessMismatch,
    UnsolvedMeta,
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
            UnsolvedMeta => write!(fmt, "unsolved meta"),
            x => write!(fmt, "Type error: {:?}", x),
        }
    }
}

impl error::Error for Error {}

// /// Pair of unforced value and forced value.
// struct Glued(Value, Value);

#[derive(Clone, Debug)]
enum SymbolValue {
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
    fn index(&self, m: MetaVar) -> &Self::Output {
        &self.0[m.0]
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
        fmt.debug_set()
            .entries(self.map.iter().map(|(Lvl(x), Lvl(y))| (x, y)))
            .finish()
    }
}

struct GlobalCtx<'w> {
    db: &'w dyn crate::Db,
    meta_ctx: MetaCtx,
    program: Option<raw::Program>,
}

/// Elaboration context.
struct Ctx<'w> {
    g: GlobalCtx<'w>,
    /// Local evaluation environment.
    env: Env,
    /// Mask of what entries in the local context metas abstract over.
    bds: Vec<bool>,
    /// Symbol table.
    table: HashMap<Id, SymbolValue>,
}

impl<'w> Ctx<'w> {
    fn new(db: &'w dyn crate::Db, program: Option<raw::Program>) -> Self {
        Self {
            g: GlobalCtx {
                db,
                meta_ctx: MetaCtx::new(),
                program,
            },
            env: Env::new(),
            bds: Vec::new(),
            table: HashMap::new(),
        }
    }

    fn fresh_meta(&mut self) -> Term {
        let meta_var = self.g.meta_ctx.fresh();
        // Contextual metavariables means creating a function that
        // abstracts over the bound variables in scope.
        Term::InsertedMeta(meta_var, self.bds.clone())
    }

    /// The normalization function.
    #[allow(unused)]
    fn nf(&mut self, t: Term) -> Term {
        let v = t.eval(&self.g, &self.env);
        v.quote(&self.g, self.env.lvl())
    }

    fn invert(&self, gamma: Lvl, spine: Spine) -> Option<PartialRenaming> {
        let dom = spine.0.len();
        let renaming = spine.0.into_iter().enumerate().try_fold(
            HashMap::new(),
            |mut renaming, (y, (v, _))| match v.force(&self.g) {
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

        Ok(match v.force(&self.g) {
            Value::Flex(m2, _) if m == m2 => return Err(Error::UnificationFailure),
            Value::Flex(m2, spine) => go_spine(Term::Meta(m2), spine)?,

            Value::Rigid(x, spine) => {
                let x2 = *renaming.map.get(&x).ok_or(Error::UnificationFailure)?;
                go_spine(Term::Local(x2.to_idx(Lvl(renaming.dom))), spine)?
            }

            Value::Abs(i, t) => Term::Abs(
                i,
                Box::new(self.rename(
                    m,
                    &renaming.clone().lift(),
                    t.apply(&self.g, Value::Rigid(Lvl(renaming.cod), Spine::new())),
                )?),
            ),

            Value::Pi(i, a, b) => Term::Pi(
                i,
                Box::new(self.rename(m, renaming, *a)?),
                Box::new(self.rename(
                    m,
                    &renaming.clone().lift(),
                    b.apply(&self.g, Value::Rigid(Lvl(renaming.cod), Spine::new())),
                )?),
            ),

            Value::Type => Term::Type,
        })
    }

    /// Solve the problem:
    ///
    ///    ?α spine =? rhs
    fn solve(&mut self, gamma: Lvl, m: MetaVar, spine: Spine, rhs: Value) -> Result<(), Error> {
        let is = spine.0.iter().map(|(_, i)| *i);
        let renaming = self
            .invert(gamma, spine.clone())
            .ok_or(Error::UnificationFailure)?;
        let rhs = self.rename(m, &renaming, rhs)?;
        let solution = is
            .rev()
            .fold(rhs, |t, i| Term::Abs(i, Box::new(t)))
            .eval(&self.g, &Env::new());
        self.g.meta_ctx.0[m.0] = MetaEntry::Solved(solution);
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
        match (v1.force(&self.g), v2.force(&self.g)) {
            (Value::Abs(_, t1), Value::Abs(_, t2)) => self.unify(
                l.inc(),
                t1.apply(&self.g, Value::Rigid(l, Spine::new())),
                t2.apply(&self.g, Value::Rigid(l, Spine::new())),
            ),
            (t1, Value::Abs(i, t2)) | (Value::Abs(i, t2), t1) => self.unify(
                l.inc(),
                t1.apply(&self.g, i, Value::Rigid(l, Spine::new())),
                t2.apply(&self.g, Value::Rigid(l, Spine::new())),
            ),
            (Value::Type, Value::Type) => Ok(()),
            (Value::Pi(i1, a1, b1), Value::Pi(i2, a2, b2)) if i1 == i2 => {
                self.unify(l, *a1, *a2)?;
                self.unify(
                    l.inc(),
                    b1.apply(&self.g, Value::Rigid(l, Spine::new())),
                    b2.apply(&self.g, Value::Rigid(l, Spine::new())),
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
        }
    }

    /// Run the function in this context extended with a bound
    /// variable/definition (TODO).
    fn with<R>(&mut self, x: Option<(Id, Vtype)>, f: impl FnOnce(&mut Ctx) -> R) -> R {
        let l = self.env.lvl();
        self.env.0.push(Value::Rigid(l, Spine::new()));
        self.bds.push(true);
        let (id, old_sym) = if let Some((id, a)) = x {
            (Some(id), self.table.insert(id, SymbolValue::Local(l, a)))
        } else {
            (None, None)
        };

        let result = f(self);

        if let Some(id) = id {
            if let Some(sym) = old_sym {
                self.table.insert(id, sym);
            } else {
                self.table.remove(&id);
            }
        }
        self.bds.pop();
        self.env.0.pop();

        result
    }

    fn close_value(&mut self, v: Value) -> Closure {
        Closure(self.env.clone(), v.quote(&self.g, self.env.lvl().inc()))
    }

    /// Insert fresh implicit applications.
    fn insert_implicits(&mut self, mut t: Term, mut va: Vtype) -> (Term, Vtype) {
        loop {
            match va.force(&self.g) {
                Value::Pi(Implicit, _a, b) => {
                    let m = self.fresh_meta();
                    t = Term::App(Box::new(t), Implicit, Box::new(m.clone()));
                    va = b.apply(&self.g, m.eval(&self.g, &self.env));
                }
                va => break (t, va),
            }
        }
    }

    fn infer(&mut self, term: &raw::Term) -> Result<(Term, Vtype), Error> {
        Ok(match term {
            raw::Term::Var(x) => {
                if let Some(s) = self.table.get(x) {
                    match s {
                        SymbolValue::Local(x, a) => {
                            (Term::Local(x.to_idx(self.env.lvl())), a.clone())
                        }
                    }
                } else if let Some(program) = self.g.program {
                    // TODO Support recursion by storing computed type
                    // of current definition entity in Ctx.
                    let Definition::Constant { ty, .. } = elaborate(self.g.db, program, *x)?;
                    let vty = ty.eval(&self.g, &Env::default());
                    (Term::Global(*x), vty)
                } else {
                    return Err(Error::NotInScope(x.text(self.g.db).to_owned()));
                }
            }

            raw::Term::Abs(i, x, t) => {
                let i = *i;
                let a = self.fresh_meta().eval(&self.g, &self.env);
                let (t, b) = match self.with(Some((*x, a.clone())), |ctx| ctx.infer(t.as_ref()))? {
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
                let (a, b) = match tty.force(&self.g) {
                    Value::Pi(i2, _, _) if i != i2 => return Err(Error::IcitnessMismatch),
                    Value::Pi(_i2, a, b) => (*a, b),
                    tty => {
                        let a = self.fresh_meta().eval(&self.g, &self.env);
                        let b = Closure(self.env.clone(), self.with(None, |ctx| ctx.fresh_meta()));
                        self.unify(
                            self.env.lvl(),
                            tty,
                            Value::Pi(i, Box::new(a.clone()), b.clone()),
                        )?;
                        (a, b)
                    }
                };
                let u = self.check(u, a)?;
                let v = b.apply(&self.g, u.eval(&self.g, &self.env));
                (Term::App(Box::new(t), i, Box::new(u)), v)
            }

            raw::Term::Type => (Term::Type, Value::Type),

            raw::Term::Pi(i, x, a, b) => {
                let a = self.check(a.as_ref(), Value::Type)?;
                let b = self.with(x.map(|x| (x, a.eval(&self.g, &self.env))), |ctx| {
                    ctx.check(b.as_ref(), Value::Type)
                })?;
                (Term::Pi(*i, Box::new(a), Box::new(b)), Value::Type)
            }

            raw::Term::Hole => {
                let t = self.fresh_meta();
                let a = self.fresh_meta().eval(&self.g, &self.env);
                (t, a)
            }

            raw::Term::Number(_) => todo!(),
        })
    }

    fn check(&mut self, t: &raw::Term, a: Vtype) -> Result<Term, Error> {
        Ok(match (t, a.force(&self.g)) {
            (raw::Term::Abs(i2, x, t), Value::Pi(i, a, b)) if i == *i2 => {
                let l = self.env.lvl();
                Term::Abs(
                    i,
                    Box::new(self.with(Some((*x, *a)), |ctx| {
                        let x =
                            ctx.check(t.as_ref(), b.apply(&ctx.g, Value::Rigid(l, Spine::new())));
                        x
                    })?),
                )
            }
            // Otherwise, if Pi is implicit, wrap in new implicit lambda
            (_, Value::Pi(Implicit, _a, b)) => {
                let l = self.env.lvl();
                let tty = self.with(None, |ctx| b.apply(&ctx.g, Value::Rigid(l, Spine::new())));
                Term::Abs(Implicit, Box::new(self.check(t, tty)?))
            }

            (raw::Term::Hole, _) => self.fresh_meta(),

            (t, expected) => {
                let (t, inferred) = self.infer(t)?;
                self.unify(self.env.lvl(), expected, inferred)?;
                t
            }
        })
    }
}

/// Elaborates a top-level definition.
#[salsa::tracked]
pub fn elaborate(db: &dyn crate::Db, program: raw::Program, name: Id) -> Result<Definition, Error> {
    let def = &program.defs(db)[&name];

    let mut ctx = Ctx::new(db, Some(program));
    Ok(match def {
        raw::Definition::Constant { name, ty, value } => {
            let (mut t, vty) = if let Some(ty) = ty {
                let ty = ctx.check(ty, Vtype::Type)?;
                let vty = ty.eval(&ctx.g, &ctx.env);
                let t = ctx.check(value, vty.clone())?;
                (t, vty)
            } else {
                ctx.infer(value)?
            };
            let mut ty = vty.quote(&ctx.g, ctx.env.lvl());
            t.zonk(&ctx.g, &mut ctx.env)?;
            ty.zonk(&ctx.g, &mut ctx.env)?;
            Definition::Constant {
                name: name.text(db).clone(),
                ty,
                value: t,
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::parse_term;

    /// Helper function for unit tests.
    fn infer(db: &dyn crate::Db, s: &str) -> Result<(Term, Type), Error> {
        let t = parse_term(db, Lexer::new(s)).unwrap();
        let mut ctx = Ctx::new(db, None);
        let (mut t, vty) = ctx.infer(&t)?;
        let ty = vty.quote(&ctx.g, ctx.env.lvl());
        t.zonk(&ctx.g, &mut ctx.env)?;
        Ok((t, ty))
    }

    #[test]
    fn test_elaborate_id() -> Result<(), Box<dyn error::Error>> {
        let db = crate::db::Database::default();
        assert_eq!(
            infer(&db, r"\x -> x")?,
            (
                Term::Abs(Explicit, Box::new(Term::Local(Idx(0)))),
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
        let db = crate::db::Database::default();
        assert_eq!(
            infer(&db, "(x : Type) -> Type")?,
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
        let db = crate::db::Database::default();
        assert_eq!(infer(&db, r"\x -> x x"), Err(Error::UnificationFailure));
    }
}
