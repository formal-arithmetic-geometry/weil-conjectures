/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase
public import Sheaf.Paper.PodReindexingHomCoefficientDescent

/-! # Identification of the integral comparison with the normalized comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
(blueprint: stage3-derived-automorphism-continuation-a-integral-comparison-identification).
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

/-- The normalized comparison is the evaluation-defined partial comparison.

Source: Stacks Project, Tag 0GMX, proof Steps 8--11.  The normalized integral
comparison is characterized by its completion-unit equation.  Expand the
completion-unit normalization and use the defining transposition of
`podIntegralClosed`; parameter naturality and the tensor comparison identify its
transpose with the inverse-transpose formula defining
`podPartialHomComparison`.  Since each closed transposition is an additive
equivalence, equality of these transposes gives equality of the arrows.

(blueprint: stage3-derived-automorphism-continuation-a-integral-comparison-identification).
Proof: expand the normalization, compare inverse transposes, and apply injectivity
of the closed additive equivalence. -/
theorem podIntegralHomComparison_eq_integralComparison :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
        (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
          (canonicalIntegralPullbackTensor l E g) P =
        (PodCoefficientDescent.integralComparison l E g).hom.app P := by
  sorry

end WeilConjectures
