/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeProper
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# `Rj_! ≅ D(j_!)` and the restriction of scalars

For a quasi-compact open immersion `j : U ⟶ Y` over a quasi-compact `Y` and a morphism of finite
coefficient rings `ρ : Λ →+* Λ'`, the identification `Rj_! ≅ D(j_!)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoOfIsOpenImmersion`) is compatible with the
commutations of the restriction of scalars with `Rj_!`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso`) and with `D(j_!)`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`):
`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekIsoOfIsOpenImmersion`.
On the way, `R(𝟙)_* ≅ 𝟭` is compatible with the restriction of scalars
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarIdIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') [Finite Λ]
  [Finite Λ']

omit [Finite Λ] in
/-- `R(𝟙 Y)_! ≅ R(𝟙 Y)_*` followed by `R(𝟙 Y)_* ≅ 𝟭` is `R(𝟙 Y)_! ≅ 𝟭`. -/
lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_comp_rightDerivedLowerShriekIdIso_hom
    (Y : Scheme.{u}) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 Y)).inv ≫
        (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).hom =
      (rightDerivedLowerStarIdIso Λ Y).hom := by
  ext K
  simp [rightDerivedLowerShriekIdIso, rightDerivedLowerStarIdIso,
    rightDerivedFunctorNatIso_hom_app_comp_isoMapDerivedCategory_hom_app_assoc]

omit [Finite Λ'] in
/-- **`R(𝟙 Y)_* ≅ 𝟭` is compatible with restriction of scalars**, through the commutation of
`Res` with `R(𝟙 Y)_*` and the unitors. -/
theorem coeffCompatible_rightDerivedLowerStarIdIso (Y : Scheme.{u}) [CompactSpace Y] (d : ℕ)
    (hd : ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((𝟙 Y)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ (𝟙 Y) d hd)
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (rightDerivedLowerStarIdIso Λ Y).hom (rightDerivedLowerStarIdIso Λ' Y).hom := by
  have h :=
    (coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar ρ (𝟙 Y) d hd).inv.comp
    (coeffCompatible_rightDerivedLowerShriekIdIso ρ Y)
  rwa [rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_comp_rightDerivedLowerShriekIdIso_hom,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_inv_comp_rightDerivedLowerShriekIdIso_hom] at h

/-- Blueprint `det-sp-purity-coefficient-change`: **`Rj_! ≅ D(j_!)` is compatible with
restriction of scalars.** For a quasi-compact open immersion `j : U ⟶ Y` with `Y` quasi-compact,
the identifications `Rj_! ≅ D(j_!)` over `Λ` and `Λ'` are related by the commutations of `Res`
with `Rj_!` and with `D(j_!)`. The identification is the change of compactification to
`U ⟶[j] Y ⟶[𝟙] Y`
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekOfCompactificationIso`)
followed by `R(𝟙 Y)_* ≅ 𝟭`
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarIdIso`). -/
theorem coeffCompatible_rightDerivedLowerShriekIsoOfIsOpenImmersion {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j] [CompactSpace Y] :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ j)
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
      (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).hom
      (rightDerivedLowerShriekIsoOfIsOpenImmersion Λ' j).hom := by
  have hd := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite (𝟙 Y)
  have h₁ := (coeffCompatible_rightDerivedLowerShriekOfCompactificationIso ρ
    (Compactification.ofIsOpenImmersion j) (HasCompactification.compactification j)).inv
  have h₂ := CoeffCompatible.whiskerLeft
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
    (coeffCompatible_rightDerivedLowerStarIdIso ρ Y hd.choose hd.choose_spec)
  have h₃ : CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm))
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
      (Functor.rightUnitor D((j)_!open[ModuleCat.{u + 1} Λ])).hom
      (Functor.rightUnitor D((j)_!open[ModuleCat.{u + 1} Λ'])).hom := fun K ↦ by
    simp [pasteTwoSquaresIso_hom_app]
  exact h₁.comp (h₂.comp h₃)

end AlgebraicGeometry.Etale
