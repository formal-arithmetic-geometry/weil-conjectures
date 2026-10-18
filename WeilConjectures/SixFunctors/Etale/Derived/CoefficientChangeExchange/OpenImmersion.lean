/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange.Basic

/-!
# Coefficient comparisons and the base change of extension by zero
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the
composition isomorphism `h^* ≅ g₂^* ⋙ g₁^*` for any `h = g₁ ≫ g₂`, componentwise. -/
@[reassoc]
lemma upperStarRestrictScalarsIso_hom_app_comp_map_upperStarComp {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (h : T ⟶ R) (hh : h = g₁ ≫ g₂)
    (N : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ h).hom.app N ≫
        (Sheaf.restrictScalars _ ρ).map ((upperStarComp _ g₁ g₂ h hh).hom.app N) =
      (upperStarComp _ g₁ g₂ h hh).hom.app ((Sheaf.restrictScalars _ ρ).obj N) ≫
        (g₁)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ g₂).hom.app N) ≫
        (upperStarRestrictScalarsIso ρ g₁).hom.app ((g₂)^*[ModuleCat.{u + 1} Λ'].obj N) := by
  subst hh
  simpa using NatTrans.congr_app (upperStarRestrictScalarsIso_comp_hom ρ g₁ g₂) N

/-- Compatibility of `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` with the square
isomorphism `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of a commutative square, componentwise. -/
@[reassoc]
lemma squareUpperStarIso_hom_app_restrictScalars {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (squareUpperStarIso _ sq).hom.app ((Sheaf.restrictScalars _ ρ).obj N) ≫
        (g')^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ f).hom.app N) ≫
        (upperStarRestrictScalarsIso ρ g').hom.app ((f)^*[ModuleCat.{u + 1} Λ'].obj N) =
      (f')^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIso ρ g).hom.app N) ≫
        (upperStarRestrictScalarsIso ρ f').hom.app ((g)^*[ModuleCat.{u + 1} Λ'].obj N) ≫
        (Sheaf.restrictScalars _ ρ).map ((squareUpperStarIso _ sq).hom.app N) := by
  have h₁ := upperStarRestrictScalarsIso_hom_app_comp_map_upperStarComp ρ f' g _ sq.w N
  have h₂ := upperStarRestrictScalarsIso_hom_app_comp_map_upperStarComp ρ g' f _ rfl N
  rw [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    ← h₂, ← cancel_epi ((upperStarComp _ f' g _ sq.w).hom.app _), Iso.hom_inv_id_app_assoc,
    ← reassoc_of% h₁]
  simp [← Functor.map_comp, squareUpperStarIso]

/-- Restriction of scalars commutes with the unit of `j^* ⊣ j_*` for the restriction `j^*`
along an open immersion. -/
lemma restrictScalars_map_openImmersionRestrictionLowerStarAdjunction_unit_app
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars _ ρ).map
        ((openImmersionRestrictionLowerStarAdjunction _ j).unit.app N) =
      (openImmersionRestrictionLowerStarAdjunction _ j).unit.app
        ((Sheaf.restrictScalars _ ρ).obj N) := by
  ext V : 3
  rfl

/-- Along an open immersion, `AlgebraicGeometry.Etale.upperStarRestrictScalarsIso` is the
identity of the restriction `j^*` through the identification of `j^*` with the restriction. -/
lemma upperStarRestrictScalarsIso_hom_app_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ j).hom.app N =
      (upperStarIsoOpenImmersionRestriction _ j).hom.app ((Sheaf.restrictScalars _ ρ).obj N) ≫
        (Sheaf.restrictScalars _ ρ).map
          ((upperStarIsoOpenImmersionRestriction _ j).inv.app N) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _).injective
  have hη (Γ : Type (u + 1)) [CommRing Γ]
      (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Γ)) :
      (openImmersionRestrictionLowerStarAdjunction _ j).unit.app M ≫
          (j)_*[ModuleCat.{u + 1} Γ].map ((upperStarIsoOpenImmersionRestriction _ j).inv.app M) =
        (upperStarLowerStarAdjunction _ j).unit.app M := by
    rw [upperStarIsoOpenImmersionRestriction, upperStarIsoLocalizationRestriction,
      openImmersionRestrictionLowerStarAdjunction,
      ← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction _ j)
        (localizationRestrictionLowerStarAdjunction _ j _), Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    simp
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← restrictScalars_map_unit_app ρ j N]
  rw [← hη Λ' N, Functor.map_comp, Functor.map_comp]
  simp only [upperStarIsoOpenImmersionRestriction, upperStarIsoLocalizationRestriction]
  rw [Adjunction.unit_leftAdjointUniq_hom_app_assoc,
    restrictScalars_map_openImmersionRestrictionLowerStarAdjunction_unit_app]
  rfl

/-- Restriction of scalars commutes with the unit of `res ⊣ coext` through the restriction
along an open immersion. -/
lemma openImmersionRestriction_map_restrictCoextendScalarsAdj_unit_app {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionRestriction _ j).map
        ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology ρ).unit.app M) =
      (Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology ρ).unit.app
        ((openImmersionRestriction _ j).obj M) := by
  ext V : 3
  rw [restrictCoextendScalarsAdj_unit_app_hom_app]
  exact restrictCoextendScalarsAdj_unit_app_hom_app ρ M _

/-- The unit form of `AlgebraicGeometry.Etale.openImmersionLowerShriekRestrictScalarsIso`, for
the adjunction `j_! ⊣ j^*` with the restriction `j^*`. -/
lemma unit_app_restrictScalars_comp_map_openImmersionLowerShriekRestrictScalarsIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionLowerShriekAdjunction _ j).unit.app ((Sheaf.restrictScalars _ ρ).obj K) ≫
        (openImmersionRestriction _ j).map
          ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app K) =
      (Sheaf.restrictScalars _ ρ).map ((openImmersionLowerShriekAdjunction _ j).unit.app K) := by
  apply ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology ρ).homEquiv _ _).injective
  have h := unit_conjugateEquiv_symm
    ((openImmersionLowerShriekAdjunction _ j).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (openImmersionLowerShriekAdjunction _ j))
    (𝟙 _) K
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app,
    openImmersionRestriction_map_restrictCoextendScalarsAdj_unit_app] at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.unit_naturality]
  simpa [openImmersionLowerShriekRestrictScalarsIso] using h.symm

/-- The unit form of `AlgebraicGeometry.Etale.openImmersionLowerShriekRestrictScalarsIso`, for
the adjunction `j_! ⊣ j^*` with the pullback `j^*`. -/
@[reassoc]
lemma unit_app_restrictScalars_comp_upperStar_map_openImmersionLowerShriekRestrictScalarsIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (openImmersionLowerShriekUpperStarAdjunction _ j).unit.app
        ((Sheaf.restrictScalars _ ρ).obj K) ≫
        (j)^*[ModuleCat.{u + 1} Λ].map
          ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app K) ≫
        (upperStarRestrictScalarsIso ρ j).hom.app ((j)_!open[ModuleCat.{u + 1} Λ'].obj K) =
      (Sheaf.restrictScalars _ ρ).map
        ((openImmersionLowerShriekUpperStarAdjunction _ j).unit.app K) := by
  have hn := (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).inv.naturality
    ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app K)
  rw [openImmersionLowerShriekUpperStarAdjunction_unit_app,
    openImmersionLowerShriekUpperStarAdjunction_unit_app, upperStarRestrictScalarsIso_hom_app_eq,
    Category.assoc, ← reassoc_of% hn, Iso.inv_hom_id_app_assoc,
    reassoc_of% unit_app_restrictScalars_comp_map_openImmersionLowerShriekRestrictScalarsIso,
    Functor.map_comp]

/-- Restriction of scalars intertwines the base change maps `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*` of the
extension by zero over `Λ'` and over `Λ`, through the coefficient comparisons of the pullbacks
and of the extensions by zero. -/
lemma coeffCompatible_openImmersionLowerShriekBaseChangeMap {U' U X' X : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g'' : X' ⟶ X} [IsOpenImmersion j]
    [IsOpenImmersion j'] (sq : CommSq g' j' j g'') :
    CoeffCompatible
      (pasteTwoSquaresIso (upperStarRestrictScalarsIso ρ g')
        (openImmersionLowerShriekRestrictScalarsIso ρ j'))
      (pasteTwoSquaresIso (openImmersionLowerShriekRestrictScalarsIso ρ j)
        (upperStarRestrictScalarsIso ρ g''))
      (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) sq)
      (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') sq) := by
  intro K
  rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app]
  apply ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j').homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← Iso.cancel_iso_hom_right _ _ ((upperStarRestrictScalarsIso ρ j').app _)]
  simp only [Iso.app_hom, Functor.comp_obj, Functor.map_comp, Category.assoc]
  have hn₁ := (upperStarRestrictScalarsIso ρ j').hom.naturality
    ((openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') sq).app K)
  have hs := (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.flip).hom.naturality
    ((openImmersionLowerShriekRestrictScalarsIso ρ j).hom.app K)
  have hO := congrArg (g')^*[ModuleCat.{u + 1} Λ].map
    (unit_app_restrictScalars_comp_upperStar_map_openImmersionLowerShriekRestrictScalarsIso ρ j K)
  have hn₂ := (upperStarRestrictScalarsIso ρ g').hom.naturality
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at hn₁ hs hO hn₂
  rw [Adjunction.unit_naturality_assoc, hn₁,
    unit_app_restrictScalars_comp_upperStar_map_openImmersionLowerShriekRestrictScalarsIso_assoc,
    unit_map_openImmersionLowerShriekBaseChangeMap_app_assoc, ← reassoc_of% hs,
    squareUpperStarIso_hom_app_restrictScalars, reassoc_of% hO, reassoc_of% hn₂,
    ← Functor.map_comp, ← Functor.map_comp, unit_map_openImmersionLowerShriekBaseChangeMap_app]

/-- The base change isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` of the extension by
zero is compatible with the coefficient comparisons. -/
lemma coeffCompatible_derivedOpenImmersionLowerShriekBaseChangeIso {U' U X' X : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g'' : X' ⟶ X} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') :
    CoeffCompatible
      (pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ g')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j'))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (leftDerivedUpperStarRestrictScalarsIso ρ g''))
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ') hsq).hom := by
  exact ((CoeffCompatible.of_conj _ _ _).whiskerRight
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')).comp <|
    ((CoeffCompatible.mapDerivedCategoryCompIso _ _).inv.comp <|
      (CoeffCompatible.mapDerivedCategoryNatIso
        (β := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap _ hsq))
        (β' := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap _ hsq))
        (coeffCompatible_openImmersionLowerShriekBaseChangeMap ρ hsq.toCommSq)).comp
        (CoeffCompatible.mapDerivedCategoryCompIso _ _)).comp <|
    (CoeffCompatible.of_conj _ _ _).inv.whiskerLeft
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)

end AlgebraicGeometry.Etale
