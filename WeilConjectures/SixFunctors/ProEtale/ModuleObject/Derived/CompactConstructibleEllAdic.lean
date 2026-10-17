/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts

/-!
# Compactness of constructible sheaves with `ℓ`-adic coefficients

For the `ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ` on a separated finite-type scheme `X` over a
field `k` which is finite or separably closed, every constructible sheaf placed in degree `0` is
compact in `Loc(Dᵇc(X, Λ))` (blueprints `sk-thm-constructible-compactness`,
`sk-prop-int-compactness`):

* `AlgebraicGeometry.ProEtale.CondensedRing.isCompactObj_singleFunctor_continuousMapRingObj`,
* `AlgebraicGeometry.ProEtale.CondensedRing.isCompactObj_singleFunctor_padicIntegersRingObj`,
* `AlgebraicGeometry.ProEtale.CondensedRing.isCompactObj_singleFunctor_padicAlgClRingObj`.

They follow from the abstract argument
`AlgebraicGeometry.ProEtale.isCompactObj_singleFunctor_of_isIndConstructibleHeart` (finite
window, left completeness of the pro-étale derived category by repleteness,
`AlgebraicGeometry.ProEtale.CondensedRing.countableAB4Star_mod`) and the inputs below.

## Sorried input

For each of the three coefficient rings:

* `isIndConstructibleHeart_*` (blueprints `sk-prop-ind-heart` (2), for `𝒪_E`
  `sk-lem-int-integral-heart` and `det-prop-int-compactness-compact` (1)): the ind-constructible
  sheaves are closed under kernels, cokernels, extensions and direct sums;
* `hasConstructibleExtContinuity_*` (blueprints `sk-lem-constructible-ext-continuity` (1), for
  `𝒪_E` `sk-lem-int-ext` (1)): morphisms `C ⟶ B[n]` out of a constructible sheaf `C` into a
  filtered colimit `B = colim Bᵢ` of sheaves factor through some `Bᵢ[n]`;
* `hasUniformConstructibleExtBound_*` (blueprints `sk-lem-uniform-constructible-ext`, for `𝒪_E`
  `sk-lem-int-ext` (2)): `Ext^q(C, N) = 0` for `C` constructible, `q > d_C` and all constructible
  `N`; this uses that `k` is finite or separably closed.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! ### The coefficient ring `E` -/

/-- Blueprint `sk-prop-ind-heart` (2), for the coefficient ring `E` of a finite extension `E` of
`ℚ_ℓ` and a separated finite-type `k`-scheme `X`: the ind-constructible `E`-sheaves are closed
under kernels, cokernels, extensions and direct sums. -/
theorem isIndConstructibleHeart_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    IsIndConstructibleHeart (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) :=
  sorry

/-- Blueprint `sk-lem-constructible-ext-continuity` (1), for the coefficient ring `E` of a finite
extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a
constructible `E`-sheaf `C` commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) :=
  sorry

/-- Blueprint `sk-lem-uniform-constructible-ext`, for the coefficient ring `E` of a finite
extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, `k` finite or separably
closed: `Ext^q(C, N) = 0` for `C` constructible, `q > d_C` and all constructible `N`. -/
theorem hasUniformConstructibleExtBound_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) :=
  sorry

/-! ### The coefficient ring `𝒪_E` -/

/-- Blueprints `sk-lem-int-integral-heart` and `det-prop-int-compactness-compact` (1), for the
coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type
`k`-scheme `X`: the ind-constructible `𝒪_E`-sheaves are closed under kernels, cokernels,
extensions and direct sums. -/
theorem isIndConstructibleHeart_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    IsIndConstructibleHeart (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  sorry

/-- Blueprint `sk-lem-int-ext` (1), for the coefficient ring `𝒪_E` of a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a
constructible `𝒪_E`-sheaf `C` commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  sorry

/-- Blueprint `sk-lem-int-ext` (2), for the coefficient ring `𝒪_E` of a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`, `k` finite or separably closed:
`Ext^q(C, N) = 0` for `C` constructible, `q > d_C` and all constructible `N`. -/
theorem hasUniformConstructibleExtBound_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) :=
  sorry

/-! ### The coefficient ring `ℚ̄_ℓ` -/

/-- Blueprint `sk-prop-ind-heart` (2), for the coefficient ring `ℚ̄_ℓ` and a separated finite-type
`k`-scheme `X`: the ind-constructible `ℚ̄_ℓ`-sheaves are closed under kernels, cokernels,
extensions and direct sums. -/
theorem isIndConstructibleHeart_padicAlgClRingObj {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    IsIndConstructibleHeart (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  sorry

/-- Blueprint `sk-lem-constructible-ext-continuity` (1), for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a constructible `ℚ̄_ℓ`-sheaf `C`
commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  sorry

/-- Blueprint `sk-lem-uniform-constructible-ext`, for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`, `k` finite or separably closed: `Ext^q(C, N) = 0` for `C`
constructible, `q > d_C` and all constructible `N`. -/
theorem hasUniformConstructibleExtBound_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k) :
    HasUniformConstructibleExtBound (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) :=
  sorry

/-! ### Compactness -/

/-- Blueprint `sk-thm-constructible-compactness` (`det-constructible-compactness-sheaf`): for the
coefficient ring `E` of a finite extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`,
`k` finite or separably closed, a constructible sheaf placed in degree `0` is compact in
`Loc(Dᵇc(X)⟦E⟧)`. -/
theorem isCompactObj_singleFunctor_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X))
    (hM : IsConstructibleModuleObject _ M)
    (hL : (boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E)
      X)).localizingClosure ((DerivedCategory.singleFunctor _ 0).obj M)) :
    BrownRepresentability.IsCompactObj
      (⟨(DerivedCategory.singleFunctor _ 0).obj M, hL⟩ : ObjectProperty.FullSubcategory
        (boundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)).localizingClosure) :=
  isCompactObj_singleFunctor_of_isIndConstructibleHeart
    (isIndConstructibleHeart_continuousMapRingObj ℓ E aX)
    (.of_continuity (hasConstructibleExtContinuity_continuousMapRingObj ℓ E aX)
      (hasUniformConstructibleExtBound_continuousMapRingObj ℓ E aX hk)) M hM hL

/-- Blueprint `sk-prop-int-compactness` (`det-prop-int-compactness-compact` (3)): for the
coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type
`k`-scheme `X`, `k` finite or separably closed, a constructible sheaf placed in degree `0` is
compact in `Loc(Dᵇc(X)⟦𝒪_E⟧)`. -/
theorem isCompactObj_singleFunctor_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X))
    (hM : IsConstructibleModuleObject _ M)
    (hL : (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E)
      X)).localizingClosure ((DerivedCategory.singleFunctor _ 0).obj M)) :
    BrownRepresentability.IsCompactObj
      (⟨(DerivedCategory.singleFunctor _ 0).obj M, hL⟩ : ObjectProperty.FullSubcategory
        (boundedConstructible
          (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)).localizingClosure) :=
  isCompactObj_singleFunctor_of_isIndConstructibleHeart
    (isIndConstructibleHeart_padicIntegersRingObj ℓ E aX)
    (.of_continuity (hasConstructibleExtContinuity_padicIntegersRingObj ℓ E aX)
      (hasUniformConstructibleExtBound_padicIntegersRingObj ℓ E aX hk)) M hM hL

/-- Blueprint `sk-thm-constructible-compactness` (`det-constructible-compactness-sheaf`): for the
coefficient ring `ℚ̄_ℓ` and a separated finite-type `k`-scheme `X`, `k` finite or separably
closed, a constructible sheaf placed in degree `0` is compact in `Loc(Dᵇc(X)⟦ℚ̄_ℓ⟧)`. -/
theorem isCompactObj_singleFunctor_padicAlgClRingObj {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (hk : Finite k ∨ IsSepClosed k)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hM : IsConstructibleModuleObject _ M)
    (hL : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ)
      X)).localizingClosure ((DerivedCategory.singleFunctor _ 0).obj M)) :
    BrownRepresentability.IsCompactObj
      (⟨(DerivedCategory.singleFunctor _ 0).obj M, hL⟩ : ObjectProperty.FullSubcategory
        (boundedConstructible
          (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)).localizingClosure) :=
  isCompactObj_singleFunctor_of_isIndConstructibleHeart
    (isIndConstructibleHeart_padicAlgClRingObj ℓ aX)
    (.of_continuity (hasConstructibleExtContinuity_padicAlgClRingObj ℓ aX)
      (hasUniformConstructibleExtBound_padicAlgClRingObj ℓ aX hk)) M hM hL

end AlgebraicGeometry.ProEtale.CondensedRing
