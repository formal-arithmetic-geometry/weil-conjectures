-- Prints the goal and inferred helper type immediately before their Kernel conversion.
module
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomCounit
public meta import HeadAuditTools
set_option maxHeartbeats 200000
set_option pp.explicit false
set_option pp.proofs false
set_option pp.universes false
set_option linter.unusedTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.IndEtaleMapping

open Lean Lean.Meta Lean.Elab.Tactic

private meta partial def firstDataDifference (label : String) (a b : Expr)
    (fuel : Nat := 40) : TacticM Bool := do
  if a == b then return false
  if (← isProp (← inferType a)) && (← isProp (← inferType b)) then
    return false
  if fuel == 0 then
    logInfo m!"{label}: fuel exhausted"
    return true
  match a, b with
  | .forallE n da ba _, .forallE _ db bb _ =>
    if ← firstDataDifference s!"{label}.domain" da db (fuel - 1) then return true
    withLocalDeclD n da fun x =>
      firstDataDifference s!"{label}.body" (ba.instantiate1 x) (bb.instantiate1 x)
        (fuel - 1)
  | _, _ =>
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    if HeadAuditTools.head a == HeadAuditTools.head b &&
        aa.size == bb.size && aa.size > 0 then
      for j in [:aa.size] do
        if ← firstDataDifference s!"{label}.{j+1}" aa[j]! bb[j]! (fuel - 1) then
          return true
      return false
    logInfo m!"{label}: {HeadAuditTools.shape a}/{HeadAuditTools.head a} vs {HeadAuditTools.shape b}/{HeadAuditTools.head b}"
    return true

elab "unfold_wrapper% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let e ← Lean.instantiateMVars e
  Lean.Core.transform e fun x => do
    if x.getAppFn.isConstOf `AlgebraicGeometry.Etale.DerivedCategoryModule then
      match (← Lean.Meta.delta? x) with
      | some y => return .done y
      | none => return .continue
    return .continue

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

example (T : Over X) : unfold_wrapper% (
    (ExternalRHom.constant A T.left ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        (imageHomIso A M K T).hom ≫
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K)).counit.app
        ((ExternalRHom.pull A T.hom).obj M) =
      (imageTensorIso A K T).hom.app
        (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T)) ≫
      ((ExternalRHom.globalAdjunction A K).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom)).counit.app
          ((ExternalRHom.pull A T.hom).obj M)) := by
  have h := conjugateEquiv_counit
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T).hom ((ExternalRHom.pull A T.hom).obj M)
  run_tac do Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getFVarFromUserName `h
    let actual ← Lean.Meta.inferType h
    let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
    HeadAuditTools.pair actual expected
    let actual := (← Lean.instantiateMVars actual).consumeMData
    let expected := (← Lean.instantiateMVars expected).consumeMData
    let _ ← firstDataDifference "nonproof" actual expected
  sorry

end AlgebraicGeometry.Etale.IndEtaleMapping
