/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData

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

private theorem associator_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
    (p : F = F') (q : G = G') (r : H = H')
    (a : F ⋙ G ≅ H) (a' : F' ⋙ G' ≅ H') (ha : HEq a a') (W : C) :
    G.map ((eqToIso p).hom.app W) ≫
        (eqToIso q).hom.app (F'.obj W) ≫ a'.hom.app W =
      a.hom.app W ≫ (eqToIso r).hom.app W := by
  subst F'
  subst G'
  subst H'
  cases eq_of_heq ha
  simp

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
      (operationStageTransitionIso l Ω X E M (h.trans k)).hom.app W := by
  exact associator_transport
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 L M k)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 E M (h.trans k))
    ((stageSystem l Ω X).assoc h k)
    (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k)
    ((stageSystem_existsUnique l Ω X).exists.choose_spec.2 E L M h k) W

end WeilConjectures.CoefQbarVerdier
