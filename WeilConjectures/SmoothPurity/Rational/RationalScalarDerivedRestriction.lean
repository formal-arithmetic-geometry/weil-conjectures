/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
/-!
# Exact derived restriction of completed coefficients

This is the restriction step of the finite coefficient argument.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(2), Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.integralCoefficientSheafSystem
universe u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
/-- Actual restriction along the completed coefficient inclusion. -/
noncomputable def rationalScalarModuleRestriction :
    scalarReductionSource l F W ⥤ scalarReductionSource l E W :=
  AlgebraicGeometry.Scheme.pbcRestrict (completedCoefficientMap l E F ι W)
/-- Restriction is additive on underlying morphisms. -/
noncomputable instance rationalScalarModuleRestriction_additive :
    (rationalScalarModuleRestriction l E F ι W).Additive :=
  inferInstanceAs (AlgebraicGeometry.Scheme.pbcRestrict
    (completedCoefficientMap l E F ι W)).Additive
/-- Restriction preserves finite limits and colimits. -/
theorem rationalScalarModuleRestriction_exact :
    PreservesFiniteLimits (rationalScalarModuleRestriction l E F ι W) ∧
      PreservesFiniteColimits (rationalScalarModuleRestriction l E F ι W) :=
  ⟨AlgebraicGeometry.Scheme.pbcRestrict_limits _,
    AlgebraicGeometry.Scheme.pbcRestrict_colimits _⟩
/-- The derived functor of exact completed coefficient restriction. -/
noncomputable def rationalScalarDerivedRestriction :
    DerivedCategory (scalarReductionSource l F W) ⥤
      DerivedCategory (scalarReductionSource l E W) := by
  let := (rationalScalarModuleRestriction_exact l E F ι W).1
  let := (rationalScalarModuleRestriction_exact l E F ι W).2
  exact (rationalScalarModuleRestriction l E F ι W).mapDerivedCategory
end WeilConjectures
