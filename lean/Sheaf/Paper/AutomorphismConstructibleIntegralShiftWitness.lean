/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.IntegralPullbackShiftCoordinates
public import Sheaf.Paper.IntegralComparisonSystemData
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! Auxiliary witness for the normalized integral shift square.
(blueprint: lem-sf-automorphism-constructible-stage-equivalence) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The normalized integral shift data and square shift compatibility.
Source: the canonical shift paragraph of the Weil-structures proof
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
The proof constructs the signed Roos shifts from a strict finite pullback tower,
transports them through the completed comparison, and checks the normalized square
on the whole system before restriction to the constructible subcategories. -/
theorem automorphismConstructibleStage_integral_shift_witness
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom)
    (b : constructibleIntegralPullback l E f ⋙
      constructibleIntegralPullback l E eY.hom ≅
      constructibleIntegralPullback l E eX.hom ⋙
        constructibleIntegralPullback l E f)
    (hb : ∀ K : sfIntegralConstructibleCategory l E X,
      (b.hom.app K).hom =
        (integralComparisonComposition l E C eY.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
          (integralComparisonComposition l E C f eX.hom K).hom) :
    ∃ (cf : (constructibleIntegralPullback l E f).CommShift ℤ)
      (cX : (constructibleIntegralPullback l E eX.hom).CommShift ℤ)
      (cY : (constructibleIntegralPullback l E eY.hom).CommShift ℤ),
      (∃ (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
        (d : (integralDerivedPullback l E f).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E f c ∧
          IntegralCompletedComparison.ShiftDescent l E f c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
            HEq (((constructibleIntegralPullback l E f).commShiftIso
              (self := cf) r).hom.app K).hom
              (((integralDerivedPullback l E f).commShiftIso r).hom.app K.obj)) ∧
      (∃ (c : (integralOperationsPullbackComplexFunctor l E eX.hom).CommShift ℤ)
        (d : (integralDerivedPullback l E eX.hom).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E eX.hom c ∧
          IntegralCompletedComparison.ShiftDescent l E eX.hom c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
            HEq (((constructibleIntegralPullback l E eX.hom).commShiftIso
              (self := cX) r).hom.app K).hom
              (((integralDerivedPullback l E eX.hom).commShiftIso r).hom.app K.obj)) ∧
      (∃ (c : (integralOperationsPullbackComplexFunctor l E eY.hom).CommShift ℤ)
        (d : (integralDerivedPullback l E eY.hom).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E eY.hom c ∧
          IntegralCompletedComparison.ShiftDescent l E eY.hom c d ∧
          ∀ (K : sfIntegralConstructibleCategory l E Y) (r : ℤ),
            HEq (((constructibleIntegralPullback l E eY.hom).commShiftIso
              (self := cY) r).hom.app K).hom
              (((integralDerivedPullback l E eY.hom).commShiftIso r).hom.app K.obj)) ∧
      (fun [sf : (constructibleIntegralPullback l E f).CommShift ℤ]
        [sX : (constructibleIntegralPullback l E eX.hom).CommShift ℤ]
        [sY : (constructibleIntegralPullback l E eY.hom).CommShift ℤ] ↦
        (constructibleIntegralPullback l E f).IsTriangulated ∧
          (constructibleIntegralPullback l E eX.hom).IsTriangulated ∧
          (constructibleIntegralPullback l E eY.hom).IsTriangulated ∧
          NatTrans.CommShift b.hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  sorry

end WeilConjectures
