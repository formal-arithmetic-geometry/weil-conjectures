/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalizationData

/-! # Compatibility of normalized integral immersion pullbacks -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.IntegralImmersionNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsImmersion g]

/-- The normalized coefficient pullback preserves constants and all quotient maps;
its ordinary derived inverse image is linear for the published constant-section action.
Source: Stacks proetale.tex, Tags 098T and 097N; derived.tex, Tag 015F
(blueprint: lem-sf-integral-immersion-coefficient-linearity).

Proof: compose the finite-projection-normalized completed-ring identifications
with the canonical inverse-image maps of the adic datum. Projecting to every
finite quotient gives the inverse-image map of the corresponding constant
finite ring. These maps preserve constants and commute with quotient maps.
The completed projections are jointly monic, hence give both the constant
identity and the projection identities. The transition identity is the datum's
transition identity. On module inverse-image generators, scalar multiplication
by a constant r is carried to multiplication by that same r. The inverse-image
adjunction and sheafification therefore give F(r f) = r F(f) on module morphisms.
Apply this degreewise to complexes. The localized action is characterized by
its action on the localization functor, so the same identity holds for all
derived morphisms. Restricting the source to the full constructible subcategory
preserves this equality. The argument includes the empty scheme, where the
section and morphism identities hold in the zero module category. -/
theorem immersion_coefficient_linearity :
    CoefficientNormalization l E g ∧
    Functor.Linear (Padic.coefficientExtensionIntegers l E)
      ((sfIntegralConstructible l E X).ι ⋙ ordinary l E g) := by sorry

end WeilConjectures.IntegralImmersionNormalization
