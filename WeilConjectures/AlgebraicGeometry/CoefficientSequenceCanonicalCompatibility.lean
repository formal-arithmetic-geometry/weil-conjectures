/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalComparisons
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalAugmentation
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCanonicalDifferenceComponent

/-! # Compatibility of the canonical coinduced product comparisons

Source: Stacks 015F and 0941.
(blueprint: lem-coef-sequence-canonical-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.CoefficientCoinduction
universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

/-- The canonical localized projections respect augmentation and difference.
The augmentation is the localized product-unit calculation and the difference is
checked componentwise after transposition.
Source: Stacks 015F and 0941.
(blueprint: lem-coef-sequence-canonical-compatibility).
-/
theorem canonicalComparisons_compatible
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.map (complexAugmentation l E W K) ≫
        canonicalProductComparison l E W K =
        derivedAugmentation l E W (DerivedCategory.Q.obj K) ∧
      DerivedCategory.Q.map (complexDifference l E W K) ≫
        canonicalRelationsComparison l E W K =
        canonicalProductComparison l E W K ≫
          derivedDifference l E W (DerivedCategory.Q.obj K) := by
  refine ⟨canonicalAugmentationComparison l E W K, ?_⟩
  apply Pi.hom_ext
  intro n
  apply ((derivedAdjunction l E W (n + 1)).homEquiv _ _).symm.injective
  simpa only [Category.assoc] using canonicalDifferenceComponent l E W K n

end WeilConjectures.CoefficientCoinduction
