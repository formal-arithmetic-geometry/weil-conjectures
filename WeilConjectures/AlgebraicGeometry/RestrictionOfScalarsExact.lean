/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunction

/-!
# Exactness of restriction from finite to completed integral coefficients

The index `n: ℕ` denotes the positive exponent `n + 1`, following the coefficient
construction. Exactness of an additive functor between abelian categories is expressed
by preservation of finite limits and finite colimits.

## References

* [Stacks Project, Tag 1456](https://stacks.math.columbia.edu/tag/1456)
* [Stacks Project, Tag 03DA](https://stacks.math.columbia.edu/tag/03DA)
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

/-- Restriction along the reduction from the completed coefficient sheaf to exponent
`n + 1` is exact. The target is modules over the completed ring sheaf, rather than
modules over the discrete constant valuation-ring sheaf. -/
theorem completedIntegralRestrictScalars_exact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E Y D hl n) ∧
      PreservesFiniteColimits (completedIntegralRestrictScalars l E Y D hl n) := by
  let α := (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n)
  have hα : α = completedIntegralCoefficientProjection l E Y D hl n := by
    ext U x
    rfl
  change PreservesFiniteLimits (SheafOfModules.restrictScalars
      (completedIntegralCoefficientProjection l E Y D hl n)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars
      (completedIntegralCoefficientProjection l E Y D hl n))
  rw [← hα]
  simpa [α, scalarReductionRestriction, scalarReductionSource, scalarReductionTarget] using
    (scalarReductionRestriction_exact l E Y n)

end WeilConjectures
