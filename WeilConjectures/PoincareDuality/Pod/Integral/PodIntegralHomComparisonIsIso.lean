/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonComparisonIdentification

/-! # Invertibility of the integral pullback Hom comparison

We prove the invertibility field of `podIntegralHomComparison_laws`.

## Main statements

* `podIntegralHomComparison_isIso`: the integral pullback Hom comparison is an isomorphism
  on every Hom-constructible pair.

## Implementation details

Reindexing along an isomorphism of sites is an exact equivalence preserving K-flat and
K-injective complexes, and its ambient Hom comparison is an isomorphism for arbitrary inputs.
On complete inputs the comparison `podPartialHomComparison` is identified with the
restriction of this ambient isomorphism (`podIntegralHomComparison_eq_integralComparison`),
and a full-subcategory arrow whose underlying arrow is invertible is invertible.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
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

/-- Invertibility component of the integral pullback Hom compatibility: for every
Hom-constructible pair `P`, the Hom comparison at `P` is an isomorphism. -/
theorem podIntegralHomComparison_isIso :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      IsIso (podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) P) := by
  intro P
  rw [podIntegralHomComparison_eq_integralComparison l E g P]
  infer_instance

end WeilConjectures
