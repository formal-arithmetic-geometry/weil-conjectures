/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonComparisonIdentification

/-! # Invertibility of the integral pullback Hom comparison

Source: Stacks Project, Tag 0GMX.

The invertibility field of `podIntegralHomComparison_laws`, left as a statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Invertibility component of the integral pullback Hom compatibility.
Source: Stacks 0GMX. -/
theorem podIntegralHomComparison_isIso :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      IsIso (podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P) := by
  intro P
  rw [podIntegralHomComparison_eq_integralComparison l E g P]
  infer_instance

end WeilConjectures
