/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionComplete
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionReductionConstructible

/-!
# Constructibility under completed coefficient restriction

This is the finite coefficient restriction step.

## Implementation details

The normalized completed coefficient presentations are identified by `purCoefficientIso`;
completeness then follows from `pbcScalarRestrictionComplete` and
`purCoefficientModel_predicates`. For the reductions, the `𝒪_E`-uniformizer maps to a unit
times `ϖ_F ^ e`, so the `n`-th reduction of the restricted input is the restriction of the
`(e * n)`-th reduction along the induced finite quotient coefficient map. Finite constructible
stratifications, local models and cohomological bounds survive restriction.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(2), Remark 6.8.15.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- Exact completed coefficient restriction preserves the intrinsic integral
constructible predicate. -/
theorem rationalScalarDerivedRestriction_constructible
    (K : sfIntegralConstructibleCategory l F W) :
    sfIntegralConstructible l E W
      ((rationalScalarDerivedRestriction l E F ι W).obj K.obj) := by
  rw [sfIntegralConstructible]
  exact ⟨rationalScalarDerivedRestriction_complete l E F ι W K,
    rationalScalarDerivedRestriction_reduction_constructible l E F ι W K⟩

end WeilConjectures
