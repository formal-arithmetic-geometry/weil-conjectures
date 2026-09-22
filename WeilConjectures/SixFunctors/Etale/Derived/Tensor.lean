/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!

# The derived tensor product of étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme.
The category `Sheaf X.smallEtaleTopology A` of `A`-valued étale sheaves on `X` is then a
monoidal Grothendieck abelian category, so it has a derived category `D(X_ét)`, and the
K-flat machinery migrated from mathlib PR #25848 equips `D(X_ét)` with the *derived tensor
product* `- ⊗ᴸ -`, the total left derived functor of `- ⊗ -` in two variables.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensor` : the derived tensor product
  `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, with scoped notation `(X)⊗ᴸ[A]`.

## Main results

- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor` : the derived tensor product
  really is the total left derived functor of the tensor product of étale sheaves, in two
  variables.

- `AlgebraicGeometry.Etale.laxMonoidal_Q` : the localization functor
  `Q : C(X_ét) ⥤ D(X_ét)` is lax monoidal.

## Implementation notes

The monoidal structure on `Sheaf X.smallEtaleTopology A` is `Sheaf.monoidalCategory`, which
is a `local instance` in mathlib rather than a global one (it is only available once
`(J.W).IsMonoidal` holds). It is therefore activated by `attribute [local instance]` here, as
in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`. Note that the *type* of
`derivedTensor` does not mention the monoidal structure, so downstream files may use it
without re-activating the local instance.

That `D(X_ét)` is monoidal at all comes from
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, which is why
the hypotheses below are exactly the ones that instance asks of the category of étale
sheaves: monoidal closed (so that tensoring preserves colimits) and admitting functorial
flat resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]

variable (X : Scheme.{u})

variable [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

set_option debug.skipKernelTC true in
lemma test_tensorObj_kernelProbe
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj
        (DerivedCategory (Sheaf X.smallEtaleTopology A))
        _ inferInstance K L
      =
    @tensorObj
        (DerivedMonoidal DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf X.smallEtaleTopology A)
            (ComplexShape.up ℤ)))
        _ inferInstance K L := by
  rfl


set_option debug.skipKernelTC true in
lemma isLeftDerivedFunctor₂_derivedTensor_kernelProbe
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme)
    [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] :
    (curriedTensor
      (DerivedCategory
        (Sheaf X.smallEtaleTopology A))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology A)
        (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor
    (Sheaf X.smallEtaleTopology A)


end AlgebraicGeometry

/-!
## Kernel `isDefEq` diagnostics

Debug-branch scaffolding for
`SixFunctors/Etale/Derived/lean_derived_tensor_kernel_debug_handoff.md`.

Nothing below is used by the rest of the library; it is a set of `CommandElabM`
probes that call the kernel directly. All of them are driven from the (commented
out) `run_cmd` blocks at the very bottom of this file — uncomment one, then run

```
lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false \
  -Dbackward.isDefEq.respectTransparency=false -Dweak.linter.mathlibStandardSet=true \
  -Dweak.linter.style.header=false -DmaxSynthPendingDepth=3 -Dwarn.sorry=false \
  WeilConjectures/SixFunctors/Etale/Derived/Tensor.lean
```

(the `-D` flags mirror `[leanOptions]` in `lakefile.toml`; `lake env lean` does not
apply them by itself). `lean` buffers its message log, so **nothing is printed until
the whole file has finished elaborating** — a probe that takes five minutes prints
all of its output at the end, in one go. Redirect to a file and wait:

```
lake env lean <flags> …/Tensor.lean > /tmp/probe.log 2>&1
```

Inside VS Code the same output appears in the infoview when the cursor is on the
`run_cmd`, with the same "all at once, at the end" behaviour.

The probes are:

* `probeKernelDecl` — §9 of the handoff: separates `Kernel.check value` from
  `Kernel.isDefEq inferredType declaredType`, in both orientations.
* `reportSlow` — descends through `inferredType` / `declaredType` in parallel and
  reports the **minimal** subterm pairs that are still expensive, i.e. the place
  where the pathological reduction starts (handoff §10.1, §10.2).
* `explodeDecl` — navigates to one node by path and times every argument pair
  there, so one can see whether the kernel could have closed the goal by
  congruence instead of unfolding.
* `drillDecl` — repeats that automatically, always following the most expensive
  differing argument.

`hintsOf` prints the reducibility hints the kernel uses to choose an unfolding
direction in `lazy_delta_reduction_step` (handoff §8.2).
-/

open Lean Elab Command Meta

set_option linter.style.emptyLine false
set_option linter.style.longLine false

/-- §9 probe: separate `Kernel.check` from `Kernel.isDefEq`. -/
private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let lctx : LocalContext := default
  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"
  let value := info.value! true
  let declaredType := info.type
  logInfo m!"============================================================"
  logInfo m!"Kernel probe: {declName}"
  logInfo m!"value sizeWithoutSharing: {value.sizeWithoutSharing}"
  logInfo m!"declared type sizeWithoutSharing: {declaredType.sizeWithoutSharing}"
  let checkStart ← IO.monoMsNow
  let inferredType ←
    match Kernel.check env lctx value with
    | .ok ty => pure ty
    | .error _ => throwError m!"Kernel.check failed for {declName}"
  let checkEnd ← IO.monoMsNow
  logInfo m!"Kernel.check(value): {checkEnd - checkStart} ms"
  logInfo m!"inferred type sizeWithoutSharing: {inferredType.sizeWithoutSharing}"
  logInfo m!"Expr.equal inferred declared: {Expr.equal inferredType declaredType}"
  let forwardStart ← IO.monoMsNow
  let forwardResult ←
    match Kernel.isDefEq env lctx inferredType declaredType with
    | .ok result => pure result
    | .error _ => throwError m!"forward Kernel.isDefEq failed for {declName}"
  let forwardEnd ← IO.monoMsNow
  logInfo m!"Kernel.isDefEq inferred → declared: result {forwardResult}, \
    time {forwardEnd - forwardStart} ms"
  let reverseStart ← IO.monoMsNow
  let reverseResult ←
    match Kernel.isDefEq env lctx declaredType inferredType with
    | .ok result => pure result
    | .error _ => throwError m!"reverse Kernel.isDefEq failed for {declName}"
  let reverseEnd ← IO.monoMsNow
  logInfo m!"Kernel.isDefEq declared → inferred: result {reverseResult}, \
    time {reverseEnd - reverseStart} ms"
  logInfo m!"============================================================"

/-- A minimal (deepest) expensive kernel-`isDefEq` subproblem. -/
private structure SlowPair where
  path : String
  depth : Nat
  ms : Nat
  res : Option Bool
  lhs : Expr
  rhs : Expr

/-- Time one `Kernel.isDefEq` call. A kernel error is reported as `none`. -/
private def timeIsDefEq (env : Environment) (lctx : LocalContext) (t s : Expr) :
    MetaM (Nat × Option Bool) := do
  let start ← IO.monoMsNow
  let out ←
    match Kernel.isDefEq env lctx t s with
    | .ok b => pure (some b)
    | .error _ => pure none
  let stop ← IO.monoMsNow
  return (stop - start, out)

/-- `head/arity` description of an application, for log lines. -/
private def headDesc (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => s!"{n}/{e.getAppNumArgs}"
  | .fvar _ => s!"fvar/{e.getAppNumArgs}"
  | .sort _ => "Sort"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | .proj n i _ => s!"proj {n}.{i}"
  | .lit _ => "lit"
  | f => s!"{f.ctorName}"

/-- The reducibility hints the kernel uses to pick an unfolding direction. -/
private def hintsOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo v) =>
      match v.hints with
      | .opaque => "def/opaque"
      | .abbrev => "def/abbrev"
      | .regular h => s!"def/regular:{h}"
  | some (.thmInfo _) => "thm"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.ctorInfo _) => "ctor"
  | some (.recInfo _) => "rec"
  | some (.inductInfo _) => "induct"
  | some (.quotInfo _) => "quot"
  | none => "NOT FOUND"

/--
Descend through the two expressions in parallel; only *time* a pair once no strictly
smaller differing pair is expensive. The result is therefore the set of **minimal**
expensive kernel defeq subproblems — the place where the pathological path begins.

Note that the descent into an application only happens when the two head functions
are syntactically equal (universe levels included); when they are not, the node is
reported as-is and `explodeDecl`/`drillDecl` should be used to look inside it.
-/
private partial def findSlow (env : Environment) (path : String) (t s : Expr)
    (threshold : Nat) (depth : Nat) : MetaM (Array SlowPair) := do
  if t.equal s then return #[]
  if depth ≤ 60 then
    match t, s with
    | .mdata _ a, _ => return (← findSlow env path a s threshold (depth + 1))
    | _, .mdata _ a => return (← findSlow env path t a threshold (depth + 1))
    | .forallE n d b _, .forallE _ d' b' _ =>
        let accD ← findSlow env (path ++ "/∀dom") d d' threshold (depth + 1)
        let accB ← withLocalDeclD n d fun x =>
          findSlow env (path ++ "/∀body") (b.instantiate1 x) (b'.instantiate1 x)
            threshold (depth + 1)
        let acc := accD ++ accB
        if !acc.isEmpty then return acc
    | .lam n d b _, .lam _ d' b' _ =>
        let accD ← findSlow env (path ++ "/λdom") d d' threshold (depth + 1)
        let accB ← withLocalDeclD n d fun x =>
          findSlow env (path ++ "/λbody") (b.instantiate1 x) (b'.instantiate1 x)
            threshold (depth + 1)
        let acc := accD ++ accB
        if !acc.isEmpty then return acc
    | .proj _ i a, .proj _ i' a' =>
        if i == i' then
          let acc ← findSlow env (path ++ s!"/proj{i}") a a' threshold (depth + 1)
          if !acc.isEmpty then return acc
    | .app .., .app .. =>
        let tf := t.getAppFn
        let sf := s.getAppFn
        let ta := t.getAppArgs
        let sa := s.getAppArgs
        if tf.equal sf && ta.size == sa.size then
          let mut acc : Array SlowPair := #[]
          for i in [0:ta.size] do
            acc := acc ++ (← findSlow env (path ++ s!"/a{i}") ta[i]! sa[i]! threshold (depth + 1))
          if !acc.isEmpty then return acc
    | _, _ => pure ()
  let lctx ← getLCtx
  let (ms, res) ← timeIsDefEq env lctx t s
  if ms < threshold then return #[]
  return #[{ path, depth, ms, res, lhs := t, rhs := s }]

/-- Run `findSlow` on the inferred-vs-declared type of `declName` and print the result. -/
private def reportSlow (declName : Name) (threshold : Nat := 2000) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"
  let value := info.value! true
  let declaredType := info.type
  let inferredType ←
    match Kernel.check env default value with
    | .ok ty => pure ty
    | .error _ => throwError m!"Kernel.check failed for {declName}"
  logInfo m!"### minimal slow kernel-isDefEq pairs for {declName} (threshold {threshold} ms)"
  let t0 ← IO.monoMsNow
  let pairs ← liftTermElabM <| findSlow env "root" inferredType declaredType threshold 0
  let t1 ← IO.monoMsNow
  logInfo m!"search wall time: {t1 - t0} ms, minimal slow pairs found: {pairs.size}"
  for p in pairs do
    logInfo m!"------------------------------------------------------------"
    logInfo m!"[DEFEQ-SLOW] depth={p.depth} ms={p.ms} result={repr p.res}"
    logInfo m!"  path = {p.path}"
    logInfo m!"  lhs head = {headDesc p.lhs}   (size {p.lhs.sizeWithoutSharing})"
    logInfo m!"  rhs head = {headDesc p.rhs}   (size {p.rhs.sizeWithoutSharing})"
    logInfo m!"  LHS := {p.lhs}"
    logInfo m!"  RHS := {p.rhs}"

/-- Time the node `t =?= s` and then every one of its argument pairs. -/
private def reportNode (env : Environment) (t s : Expr) : MetaM Unit := do
  let lctx ← getLCtx
  let (ms, res) ← timeIsDefEq env lctx t s
  logInfo m!"NODE: ms={ms} res={repr res}  lhsHead={headDesc t} rhsHead={headDesc s}  \
    sizes {t.sizeWithoutSharing}/{s.sizeWithoutSharing}"
  let ta := t.getAppArgs
  let sa := s.getAppArgs
  logInfo m!"  fn syntactically equal: {t.getAppFn.equal s.getAppFn}; #args {ta.size}/{sa.size}"
  if ta.size == sa.size then
    for i in [0:ta.size] do
      let a := ta[i]!
      let b := sa[i]!
      if a.equal b then
        logInfo m!"  arg{i}: SYNTACTICALLY EQUAL (size {a.sizeWithoutSharing})"
      else
        let (m2, r2) ← timeIsDefEq env lctx a b
        logInfo m!"  arg{i}: ms={m2} res={repr r2}  \
          sizes {a.sizeWithoutSharing}/{b.sizeWithoutSharing}  \
          heads {headDesc a} vs {headDesc b}"
        logInfo m!"     LHSarg := {a}"
        logInfo m!"     RHSarg := {b}"

/--
Navigate the two expressions along `path` and then `reportNode` there.
A path component is `"b"` (enter a `∀`-body, introducing a local) or `"aN"`
(take the `N`-th explicit-or-implicit argument of an application).
-/
private partial def explodeAt (env : Environment) (t s : Expr) (path : List String) :
    MetaM Unit := do
  match path with
  | [] => reportNode env t s
  | "b" :: rest =>
      match t, s with
      | .forallE n d b _, .forallE _ _ b' _ =>
          withLocalDeclD n d fun x => explodeAt env (b.instantiate1 x) (b'.instantiate1 x) rest
      | _, _ => throwError m!"expected forall, got {t.ctorName}/{s.ctorName}"
  | p :: rest =>
      if p.startsWith "a" then
        let i := (p.drop 1).toNat!
        explodeAt env t.getAppArgs[i]! s.getAppArgs[i]! rest
      else throwError m!"bad path component {p}"

private def explodeDecl (declName : Name) (path : List String) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | throwError m!"cannot find {declName}"
  let inferredType ←
    match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError m!"Kernel.check failed"
  liftTermElabM <| explodeAt env inferredType info.type path

private def showTerm (e : Expr) : MessageData :=
  if e.sizeWithoutSharing ≤ 2500 then m!"{e}" else m!"<size {e.sizeWithoutSharing}, elided>"

/-- Like `reportNode`, but recursively follows the most expensive differing argument. -/
private partial def drill (env : Environment) (t s : Expr) (lvl : Nat) (maxLvl : Nat) :
    MetaM Unit := do
  let lctx ← getLCtx
  let (ms, res) ← timeIsDefEq env lctx t s
  logInfo m!"[L{lvl}] NODE ms={ms} res={repr res}  \
    lhs={headDesc t}(size {t.sizeWithoutSharing})  rhs={headDesc s}(size {s.sizeWithoutSharing})  \
    fnSyntEq={t.getAppFn.equal s.getAppFn}"
  logInfo m!"[L{lvl}] LHS := {showTerm t}"
  logInfo m!"[L{lvl}] RHS := {showTerm s}"
  if lvl ≥ maxLvl then
    logInfo m!"[L{lvl}] max level reached"
    return
  let ta := t.getAppArgs
  let sa := s.getAppArgs
  if !(t.getAppFn.equal s.getAppFn) then
    logInfo m!"[L{lvl}] head functions differ: {t.getAppFn} vs {s.getAppFn}"
  if ta.size != sa.size || ta.size == 0 then
    logInfo m!"[L{lvl}] cannot descend structurally (#args {ta.size}/{sa.size}); STOP"
    return
  let mut best : Option (Nat × Nat) := none
  for i in [0:ta.size] do
    if ta[i]!.equal sa[i]! then
      logInfo m!"[L{lvl}]   arg{i}: syntactically equal"
    else
      let (m2, r2) ← timeIsDefEq env lctx ta[i]! sa[i]!
      logInfo m!"[L{lvl}]   arg{i}: ms={m2} res={repr r2}  \
        {headDesc ta[i]!}(size {ta[i]!.sizeWithoutSharing}) vs \
        {headDesc sa[i]!}(size {sa[i]!.sizeWithoutSharing})"
      match best with
      | some (_, bm) => if m2 > bm then best := some (i, m2)
      | none => best := some (i, m2)
  match best with
  | none => logInfo m!"[L{lvl}] all args syntactically equal; STOP"
  | some (i, m2) =>
      logInfo m!"[L{lvl}] ==> descending into arg{i} (ms={m2})"
      drill env ta[i]! sa[i]! (lvl + 1) maxLvl

private def drillDecl (declName : Name) (path : List String) (maxLvl : Nat) :
    CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | throwError m!"cannot find {declName}"
  let inferredType ←
    match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError m!"Kernel.check failed"
  liftTermElabM <| navigate env inferredType info.type path maxLvl
where
  navigate (env : Environment) (t s : Expr) (path : List String) (maxLvl : Nat) : MetaM Unit := do
    match path with
    | [] => drill env t s 0 maxLvl
    | "b" :: rest =>
        match t, s with
        | .forallE n d b _, .forallE _ _ b' _ =>
            withLocalDeclD n d fun x =>
              navigate env (b.instantiate1 x) (b'.instantiate1 x) rest maxLvl
        | _, _ => throwError m!"expected forall"
    | p :: rest =>
        if p.startsWith "a" then
          let i := (p.drop 1).toNat!
          navigate env t.getAppArgs[i]! s.getAppArgs[i]! rest maxLvl
        else throwError m!"bad path {p}"

/-!
### Drivers

Uncomment exactly one block and run the file as described at the top of this
section. Expect minutes, not seconds; `test_tensorObj_kernelProbe` alone is about
90 s per `Kernel.isDefEq` call and each probe makes several.

The path `["b"×12, "a2"]` reaches the two `tensorObj` applications of
`test_tensorObj_kernelProbe`: twelve `∀`-binders, then the third argument of
`@Eq α lhs rhs`, i.e. `rhs`. Appending a further `"a2"` reaches the
`MonoidalCategoryStruct` instance argument of `tensorObj`.
-/

-- set_option maxHeartbeats 0 in
-- run_cmd do
--   probeKernelDecl ``AlgebraicGeometry.test_tensorObj_kernelProbe
--   reportSlow ``AlgebraicGeometry.test_tensorObj_kernelProbe 2000

-- set_option maxHeartbeats 0 in
-- run_cmd do
--   let env ← getEnv
--   for n in [`CategoryTheory.MonoidalCategoryStruct.tensorObj,
--             `CategoryTheory.DerivedMonoidal,
--             `CategoryTheory.MonoidalCategory.ofBifunctor,
--             `CategoryTheory.DerivedMonoidal.bifunctor,
--             `CategoryTheory.Functor.leftDerived₂,
--             `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory,
--             `DerivedCategory.Qh, `DerivedCategory.Q,
--             `CategoryTheory.toDerivedMonoidal,
--             `CategoryTheory.ShrinkHoms.equivalence] do
--     logInfo m!"  {n} : {hintsOf env n}"
--   explodeDecl ``AlgebraicGeometry.test_tensorObj_kernelProbe
--     ["b","b","b","b","b","b","b","b","b","b","b","b","a2"]

-- set_option maxHeartbeats 0 in
-- run_cmd
--   drillDecl ``AlgebraicGeometry.test_tensorObj_kernelProbe
--     ["b","b","b","b","b","b","b","b","b","b","b","b","a2","a2"] 6
