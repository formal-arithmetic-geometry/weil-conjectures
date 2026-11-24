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
    (A : Type u') [Category.{u + 1, u'} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1, u + 1, u'} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] (X : Scheme.{u})
    [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    @tensorObj (DerivedCategory (Sheaf X.smallEtaleTopology A)) _ inferInstance K L =
    @tensorObj (DerivedMonoidal DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)))
      _ inferInstance K L := by
  rfl

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  logInfo m!"[LAYOUT] MonoidalCategory={getStructureFields env `CategoryTheory.MonoidalCategory}"
  logInfo m!"[LAYOUT] MonoidalCategoryStruct={getStructureFields env `CategoryTheory.MonoidalCategoryStruct}"
  let some info := env.find? ``test_tensorObj_kernelProbe | throwError "missing probe"
  let inferred ← match Kernel.check env default (info.value! true) with
    | .ok ty => pure ty
    | .error _ => throwError "check failed"
  let rec go (a b : Expr) (remaining : Nat) : MetaM Unit := do
    if remaining == 0 then
      logInfo m!"[ROOT] {a.getAppFn}/{a.getAppNumArgs} / {b.getAppFn}/{b.getAppNumArgs}"
      for i in [0:a.getAppNumArgs] do
        logInfo m!"[ROOTARG {i}] {a.getAppArgs[i]!.getAppFn}/{a.getAppArgs[i]!.getAppNumArgs} / {b.getAppArgs[i]!.getAppFn}/{b.getAppArgs[i]!.getAppNumArgs}"
      let leftProvider := (a.getAppArgs[2]!).getAppArgs[2]!
      let rightProvider := (b.getAppArgs[2]!).getAppArgs[2]!
      let leftParent ← whnf leftProvider
      let rightParent ← whnf rightProvider
      logInfo m!"[PARENT] {leftParent.getAppFn}/{leftParent.getAppNumArgs} / {rightParent.getAppFn}/{rightParent.getAppNumArgs}"
      let leftField := leftParent.getAppArgs[2]!
      let rightField := rightParent.getAppArgs[2]!
      logInfo m!"[FIELD] hash={leftField.hash}/{rightField.hash} size={leftField.sizeWithoutSharing}/{rightField.sizeWithoutSharing} equal={leftField.equal rightField}"
      logInfo m!"[FIELD LEFT] {leftField}"
      logInfo m!"[FIELD RIGHT] {rightField}"
      let t0 ← IO.monoMsNow
      let resultText ← match Kernel.isDefEq env (← getLCtx) leftField rightField with
        | .ok b => pure s!"{b}"
        | .error _ => pure "error"
      let t1 ← IO.monoMsNow
      logInfo m!"[REPLAY] result={resultText} ms={t1-t0}"
    else
      match a, b with
      | .forallE n d body _, .forallE _ _ body' _ =>
        withLocalDeclD n d fun x => go (body.instantiate1 x) (body'.instantiate1 x) (remaining-1)
      | _, _ => throwError "bad binder path"
  liftTermElabM <| go inferred info.type 12

end AlgebraicGeometry
