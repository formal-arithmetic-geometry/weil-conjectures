/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarEtaleOrigin

/-!
# Direct image and tensor product preserve `Dctf` on the pro-étale site

For a finite coefficient ring `Λ`, the pro-étale derived direct image `Rf_*` and the pro-étale
derived tensor product `⊗ᴸ` preserve the constructible finite-Tor subcategories
`Dctf(-_proét, Λ)` (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`).

Both statements are transported from their étale counterparts along the comparison pullback
`ν^*`: an object of `Dctf(X_proét, Λ)` is `ν^* G` for a bounded constructible étale complex `G`,
which has finite Tor amplitude since `ν^*` detects Tor amplitude
(`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff`). Then
`Rf_* ν^* G ≅ ν^* Rf_* G`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`) and
`ν^* G ⊗ᴸ ν^* G' ≅ ν^*(G ⊗ᴸ G')`
(`AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`).

## Main statements

- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerStar`
- `AlgebraicGeometry.ProEtale.constructibleFiniteTor_tensor`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- An object of `Dctf(X_proét, Λ)` is `ν^* G` for some `G ∈ Dctf(X_ét, Λ)`. -/
lemma exists_constructibleFiniteTor_iso_mapDerivedCategory {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    ∃ G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X G ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G ≅ K) := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
  exact ⟨G, ⟨hG, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
    ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩, ⟨e⟩⟩

/-- Blueprint `proposition-six-operations-dctf--2`: for a finite ring `Λ` whose exponent is
invertible on `Y` and a separated morphism `f : X ⟶ Y` of finite-type `k`-schemes, the pro-étale
derived direct image `Rf_*` carries `Dctf(X_proét, Λ)` into `Dctf(Y_proét, Λ)`. On `ν^* G` it is
`ν^* Rf_*^{ét} G` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`),
and the étale `Rf_*` preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`). -/
theorem constructibleFiniteTor_rightDerivedLowerStar {k : Type u} [Field k]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f] [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj K) := by
  have : QuasiCompact f := by
    subst hf
    have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    have : IsNoetherian Y := {}
    exact QuasiCompact.of_comp f aY
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_constructibleFiniteTor_iso_mapDerivedCategory Λ hK
  exact (DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso
    ((rightDerivedLowerStarMapDerivedCategoryObjIso _ f G hG.1.1.1).symm ≪≫
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso e)
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf hG))

/-- Blueprint `proposition-six-operations-dctf--14`, the finite coefficients: for a finite ring
`Λ` and `K, L ∈ Dctf(X_proét, Λ)`, the derived tensor product `K ⊗ᴸ L` lies in
`Dctf(X_proét, Λ)`. Writing `K ≅ ν^* G` and `L ≅ ν^* G'`, it is `ν^*(G ⊗ᴸ G')` (`ν^*` is
monoidal), and the étale `⊗ᴸ` preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_tensor`). -/
theorem constructibleFiniteTor_tensor {X : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_constructibleFiniteTor_iso_mapDerivedCategory Λ hK
  obtain ⟨G', hG', ⟨e'⟩⟩ := exists_constructibleFiniteTor_iso_mapDerivedCategory Λ hL
  exact (DerivedCategory.constructibleFiniteTor _ X).prop_of_iso
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ G).app G' ≪≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e).app _ ≪≫
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso e')
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_tensor Λ X hG hG'))

end AlgebraicGeometry.ProEtale
