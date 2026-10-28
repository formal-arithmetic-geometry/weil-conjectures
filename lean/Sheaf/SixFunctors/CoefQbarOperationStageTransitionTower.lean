/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData

/-! # Transition isomorphism tower coherence

(blueprint: lem-coef-qbar-operation-stage-transition-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u})

open AlgebraicallyClosedCoefficients (Index coefficientInclusion coefficientInclusion_laws)
open GeneralAlgebraicallyClosedCoefficients (Stage stageSystem stageSystem_existsUnique)

/-- The defining transition isomorphisms transport the stage-system associator.
Source: the uniqueness equations for the recorded stage system.
(blueprint: lem-coef-qbar-operation-stage-transition-tower). -/
theorem operationStageTransitionIso_tower
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M)
    (W : Stage l Ω X E) :
    ((stageSystem l Ω X).T k).map
        ((operationStageTransitionIso l Ω X E L h).hom.app W) ≫
      (operationStageTransitionIso l Ω X L M k).hom.app
        ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj W) ≫
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app W =
    ((stageSystem l Ω X).assoc h k).hom.app W ≫
      (operationStageTransitionIso l Ω X E M (h.trans k)).hom.app W := by sorry

end WeilConjectures.CoefQbarVerdier
