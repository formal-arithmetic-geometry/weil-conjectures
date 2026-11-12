/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall

/-!
# The category of ind-constructible sheaves is Grothendieck abelian

Blueprint `proposition-ind-constructible-sheaves--8`: the category `IndCons(X, Λ)` of
ind-constructible sheaves of `Λ`-modules on `X_proét` is a Grothendieck abelian category.

Once `IndCons(X, R)` is known to be closed under kernels, cokernels, extensions and direct sums
in the category of `R`-modules (`AlgebraicGeometry.ProEtale.IsIndConstructibleHeart R`), this
follows from `CategoryTheory.ObjectProperty.isGrothendieckAbelian_ind_fullSubcategory` applied
with `P` the constructible sheaves, which form an essentially small family
(`AlgebraicGeometry.ProEtale.constructibleModuleObjects_essentiallySmall`). The abelian structure
on `IndCons(X, R)` is the one of `Mathlib.CategoryTheory.Abelian.Subcategory`, obtained from the
closure properties recorded in `IsIndConstructibleHeart R`.

## Main results

* `AlgebraicGeometry.ProEtale.IsIndConstructibleHeart.isGrothendieckAbelian`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_continuousMapRingObj`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_padicIntegersRingObj`
* `AlgebraicGeometry.ProEtale.CondensedRing.isGrothendieckAbelian_padicAlgClRingObj`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

/-- Blueprint `proposition-ind-constructible-sheaves--8`: if `IndCons(X, R)` is closed under
extensions, it is closed under finite products (direct sums). -/
lemma IsIndConstructibleHeart.isClosedUnderFiniteProducts (hR : IsIndConstructibleHeart R) :
    (IsIndConstructibleModuleObject R).IsClosedUnderFiniteProducts :=
  have := hR.isClosedUnderExtensions
  ObjectProperty.isClosedUnderFiniteProducts_of_isClosedUnderExtensions _

/-- Blueprint `proposition-ind-constructible-sheaves--8`: if `IndCons(X, R)` is closed under
kernels, cokernels, extensions and direct sums, and the constructible sheaves of `R`-modules form
an essentially small family, then `IndCons(X, R)` (with the abelian structure of a full
subcategory closed under kernels, cokernels and finite products) is Grothendieck abelian. -/
theorem IsIndConstructibleHeart.isGrothendieckAbelian (hR : IsIndConstructibleHeart R)
    (hs : ObjectProperty.EssentiallySmall.{u + 1} (IsConstructibleModuleObject R)) :
    haveI := hR.isClosedUnderKernels
    haveI := hR.isClosedUnderCokernels
    haveI := hR.isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject R).FullSubcategory := by
  have := hR.isClosedUnderKernels
  have := hR.isClosedUnderCokernels
  have := hR.isClosedUnderFiniteProducts
  have := hR.isClosedUnderColimitsOfShape_discrete
  exact ObjectProperty.isGrothendieckAbelian_ind_fullSubcategory _

end General

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for sheaves of abelian groups on a
quasi-compact locally Noetherian scheme: if `IndCons(X, R)` is closed under kernels, cokernels,
extensions and direct sums, then it is Grothendieck abelian (the constructible sheaves form an
essentially small family by `constructibleModuleObjects_essentiallySmall`). -/
theorem IsIndConstructibleHeart.isGrothendieckAbelian_of_isLocallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (hR : IsIndConstructibleHeart R) :
    haveI := hR.isClosedUnderKernels
    haveI := hR.isClosedUnderCokernels
    haveI := hR.isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject R).FullSubcategory :=
  hR.isGrothendieckAbelian (constructibleModuleObjects_essentiallySmall X R)

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `E` of a
finite extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: the category
`IndCons(X, E)` of ind-constructible `E`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_continuousMapRingObj ℓ E aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_continuousMapRingObj ℓ E aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`: the category `IndCons(X, ℚ̄_ℓ)` of ind-constructible
`ℚ̄_ℓ`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_padicAlgClRingObj ℓ aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_padicAlgClRingObj ℓ aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

/-- Blueprint `proposition-ind-constructible-sheaves--8`, for the coefficient ring `𝒪_E` of a
finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: the
category `IndCons(X, 𝒪_E)` of ind-constructible `𝒪_E`-sheaves is Grothendieck abelian. -/
theorem isGrothendieckAbelian_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderKernels
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderCokernels
    haveI := (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX).isClosedUnderFiniteProducts
    IsGrothendieckAbelian.{u + 1} (IsIndConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).FullSubcategory := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  exact (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX)
    |>.isGrothendieckAbelian_of_isLocallyNoetherian

end CondensedRing

end AlgebraicGeometry.ProEtale
