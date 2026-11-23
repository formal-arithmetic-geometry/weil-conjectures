-- Measures only the final inferred-type-to-goal conversion of the concrete counit proof.
module
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomCounit
open Lean Meta
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 4096
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

example (T : Over X) :
    type_of% (conjugateEquiv_counit
      ((ExternalRHom.globalAdjunction A K).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
      (imageTensorIso A K T).hom ((ExternalRHom.pull A T.hom).obj M)) := by
  have h := conjugateEquiv_counit
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T).hom ((ExternalRHom.pull A T.hom).obj M)
  run_tac do Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getFVarFromUserName `h
    let actual ← instantiateMVars (← Lean.Meta.inferType h)
    let expected ← instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
    let env ← Lean.getEnv
    let lctx ← Lean.MonadLCtx.getLCtx
    let start ← IO.monoMsNow
    let result := Lean.Kernel.isDefEq env lctx actual expected
    let stop ← IO.monoMsNow
    Lean.logInfo m!"CCMOA frozen aligned: actual={actual.hash} expected={expected.hash} structural={actual == expected} result={match result with | .ok true => "equal" | .ok false => "unequal" | .error _ => "error"} wall_ms={stop - start}"
  sorry

end AlgebraicGeometry.Etale.IndEtaleMapping
