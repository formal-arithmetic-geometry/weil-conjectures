import WeilConjectures.SixFunctors.Etale.Derived.Tensor

open Lean Elab Command Meta
open CategoryTheory Limits MonoidalCategory
set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace AlgebraicGeometry

open Scheme

universe u' u

set_option debug.skipKernelTC true in
lemma test_tensorObj_kernelProbe
    (A : Type u')
    [Category.{u + 1, u'} A]
    [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A]
    [MonoidalCategory A]
    [MonoidalPreadditive A]
    [SymmetricCategory A]
    (X : Scheme.{u})
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

private def probeKernelDecl (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError m!"cannot find declaration {declName}"
  let value := info.value! true
  let declaredType := info.type
  let t0 ← IO.monoMsNow
  let inferredType ←
    match Kernel.check env default value with
    | .ok ty => pure ty
    | .error _ => throwError m!"Kernel.check failed"
  let t1 ← IO.monoMsNow
  logInfo m!"[R2] decl={declName} valueSize={value.sizeWithoutSharing} declaredSize={declaredType.sizeWithoutSharing}"
  logInfo m!"[R2] Kernel.check(value) ms={t1 - t0} inferredSize={inferredType.sizeWithoutSharing} equal={Expr.equal inferredType declaredType}"
  let f0 ← IO.monoMsNow
  let fr ← match Kernel.isDefEq env default inferredType declaredType with
    | .ok b => pure b
    | .error _ => throwError m!"forward isDefEq failed"
  let f1 ← IO.monoMsNow
  logInfo m!"[R2] forward result={fr} ms={f1 - f0}"
  let r0 ← IO.monoMsNow
  let rr ← match Kernel.isDefEq env default declaredType inferredType with
    | .ok b => pure b
    | .error _ => throwError m!"reverse isDefEq failed"
  let r1 ← IO.monoMsNow
  logInfo m!"[R2] reverse result={rr} ms={r1 - r0}"

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

private def timeEq (env : Environment) (a b : Expr) : MetaM (Nat × Option Bool) := do
  let t0 ← IO.monoMsNow
  let r := match Kernel.isDefEq env (← getLCtx) a b with
    | .ok x => some x
    | .error _ => none
  let t1 ← IO.monoMsNow
  pure (t1 - t0, r)

private def reportNode (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | throwError m!"cannot find declaration"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError m!"check failed"
  let path : List String := List.replicate 12 "b" ++ ["a2"]
  let rec go (a b : Expr) (ps : List String) : MetaM Unit := do
    match ps with
    | [] =>
      let aa := a.getAppArgs; let bb := b.getAppArgs
      let i := 2
      let (mi, ri) ← timeEq env aa[i]! bb[i]!
      logInfo m!"[R2 ARG] i={i} ms={mi} result={repr ri} lhs={headDesc aa[i]!} rhs={headDesc bb[i]!} sizes={aa[i]!.sizeWithoutSharing}/{bb[i]!.sizeWithoutSharing}"
    | "b" :: rest =>
      match a, b with
      | .forallE n d body _, .forallE _ _ body' _ =>
        withLocalDeclD n d fun x => go (body.instantiate1 x) (body'.instantiate1 x) rest
      | _, _ => throwError m!"bad forall path"
    | p :: rest =>
      if p.startsWith "a" then
        let i := (p.drop 1).toNat!
        go a.getAppArgs[i]! b.getAppArgs[i]! rest
      else throwError m!"unsupported path component"
  liftTermElabM <| go inferred info.type path

private def printHints : CommandElabM Unit := do
  let env ← getEnv
  let names := [`CategoryTheory.MonoidalCategoryStruct.tensorObj,
    `CategoryTheory.DerivedMonoidal, `CategoryTheory.MonoidalCategory.ofBifunctor,
    `CategoryTheory.DerivedMonoidal.bifunctor, `CategoryTheory.Functor.leftDerived₂,
    `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory,
    `DerivedCategory.Qh, `DerivedCategory.Q]
  for n in names do
    match env.find? n with
    | some (.defnInfo v) =>
      let hs := match v.hints with
        | .opaque => "def/opaque"
        | .abbrev => "def/abbrev"
        | .regular h => s!"def/regular:{h}"
      logInfo m!"[R2 HINT] {n} {hs}"
    | _ => logInfo m!"[R2 HINT] {n} unavailable"

set_option maxHeartbeats 0 in
run_cmd do
  reportNode ``test_tensorObj_kernelProbe

end AlgebraicGeometry
