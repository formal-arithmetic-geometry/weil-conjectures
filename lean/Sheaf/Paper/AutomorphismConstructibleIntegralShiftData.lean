/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.IntegralPullbackShiftCoordinates

/-! Auxiliary signed shifts for every integral pullback.
(blueprint: lem-sf-automorphism-constructible-stage-equivalence) -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Signed Roos shifts exist for every scheme morphism.
Source: the canonical shift paragraph of the Weil-structures proof
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Choose a normalized strict finite pullback tower, apply the signed mapping-cocone
construction, and descend the resulting shift through the derived comparison. -/
theorem automorphismConstructibleStage_integral_shift_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d := by
  sorry

end WeilConjectures
