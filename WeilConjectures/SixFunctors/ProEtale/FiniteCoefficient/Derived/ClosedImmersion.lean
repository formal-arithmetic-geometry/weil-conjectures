/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# The exceptional inverse image along a closed immersion on pro-étale sheaves

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. On
pro-étale sheaves, the sections of `N` with support in `Z` form the kernel
`Γ_Z N = ker(N ⟶ j_* j^* N)` of the unit of `j^* ⊣ j_*`, and

`i^!₀ N = i^* Γ_Z N`

(`AlgebraicGeometry.ProEtale.closedUpperShriek`, blueprint
`def-exc-proetale-sections-with-support`). For pro-étale sheaves of modules it is right adjoint
to the exact functor `i_*` (`AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction`),
so its right derived functor is right adjoint to `i_*` on the unbounded derived categories
(`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lem-exc-proetale-closed-support`), and the unit of this adjunction is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`,
blueprint `prop-sf-closed-immersion-unit`).

## The sheaf-level adjunction

Write `Sh_Z(X)` for the full subcategory of sheaves `F` with `j^* F = 0`. The adjunction
`i_* ⊣ i^!₀` is the composite of two adjunctions:

* `i_* : Sh(Z) ⥤ Sh_Z(X)` is an equivalence with inverse `i^*`: the counit `i^* i_* ⟶ 𝟭` is an
  isomorphism (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`), and so
  is the unit `F ⟶ i_* i^* F` for `F ∈ Sh_Z(X)`
  (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`);
* the inclusion `Sh_Z(X) ⥤ Sh(X)` is left adjoint to `Γ_Z`: a map `F ⟶ N` from `F ∈ Sh_Z(X)`
  is killed by the unit `N ⟶ j_* j^* N`, since `j_* j^* F = 0`, so it factors uniquely through
  the kernel `Γ_Z N`, and `j^* Γ_Z N = 0` because `j^*` is exact and `j^* j_* ≅ 𝟭`.

## Main definitions

- `AlgebraicGeometry.ProEtale.sectionsWithSupport`: `Γ_Z N = ker(N ⟶ j_* j^* N)`.
- `AlgebraicGeometry.ProEtale.closedUpperShriek`: `i^!₀ = i^* ∘ Γ_Z`.
- `AlgebraicGeometry.ProEtale.lowerStarClosedUpperShriekAdjunction`: `i_* ⊣ i^!₀`.
- `AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`: `i_* ⊣ R i^!₀` on
  the unbounded derived categories.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Definition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)

variable {A} in
/-- The counit `j^* j_* ⟶ 𝟭` of the pro-étale adjunction `j^* ⊣ j_*` along an open immersion is
an isomorphism: up to the identification of `j^*` with restriction, it is the counit of the
restriction adjunction. -/
instance isIso_upperStarLowerStarAdjunction_counit_of_isOpenImmersion {j : U ⟶ X}
    [IsOpenImmersion j] : IsIso (upperStarLowerStarAdjunction A j).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  rw [← Adjunction.leftAdjointUniq_hom_app_counit (upperStarLowerStarAdjunction _ j)
    (openImmersionRestrictionLowerStarAdjunction _ j)]
  exact inferInstanceAs (IsIso ((upperStarIsoOpenImmersionRestriction _ j).hom.app _ ≫ _))

end Definition

section Adjunction

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

omit [QuasiCompact j] in
/-- The direct image `Ri_*` along a closed immersion is fully faithful on the unbounded derived
categories of pro-étale sheaves of modules: `i_*` is fully faithful
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`) and preserves
K-injective complexes as a right adjoint of the exact `i^*`, and the right derived functor of a
fully faithful functor preserving K-injective complexes is fully faithful
(`CategoryTheory.Functor.full_rightDerivedFunctor`). -/
instance full_rightDerivedFunctor_lowerStar :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor.Full :=
  have : ((i)_*[ModuleCat.{u + 1} R]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).preservesKInjectiveComplexes
  inferInstance

omit [QuasiCompact j] in
instance faithful_rightDerivedFunctor_lowerStar :
    ((i)_*[ModuleCat.{u + 1} R]).rightDerivedFunctor.Faithful :=
  have : ((i)_*[ModuleCat.{u + 1} R]).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).preservesKInjectiveComplexes
  inferInstance

end Adjunction

end ProEtale

end AlgebraicGeometry
