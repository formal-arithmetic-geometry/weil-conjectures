/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! # The coefficient tower equation for rational pullback

Source: the pullback clause of `scalarOperationsOrdinary_tower`, followed by the
completed and rational comparison normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] rationalDerivedPullback sfRationalScalarExtension
  rationalPullbackScalarComparison sfRationalScalarComp HasDerivedCategory.standard
  integralDerivedPullback integralScalarExtension sfIntegralOrdinaryComparison
  completedIntegralCoefficientSheafUnrestricted integralOrdinaryScalar

attribute [local implicit_reducible] scalarReductionSourceDerived
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  sfIntegralConstructibleLinear ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup

-- A pointwise pasting calculation, independent of any coefficient or geometric model.

section Integral
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

end Integral

section Rational
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

end Rational

end WeilConjectures
