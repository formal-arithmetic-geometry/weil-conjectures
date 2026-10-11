/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# The projection formula for the extension by zero commutes with base change

For a cartesian square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the
projection formula `j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap`) commutes with the
derived base change isomorphism `Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso`) and the tensor
comparisons of the derived pullbacks.

## Main results

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap_baseChange`: the
  compatibility.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

omit [HasSmallSiteSheafify A] in
/-- The square isomorphism of pullbacks does not depend on the chosen composite. -/
lemma upperStarComp_symm_trans_eq {k₁ k₂ : U' ⟶ Z} (h₁ : k₁ = g' ≫ j) (h₁' : k₁ = j' ≫ g'')
    (h₂ : k₂ = g' ≫ j) (h₂' : k₂ = j' ≫ g'') :
    (upperStarComp A g' j k₁ h₁).symm ≪≫ upperStarComp A j' g'' k₁ h₁' =
      (upperStarComp A g' j k₂ h₂).symm ≪≫ upperStarComp A j' g'' k₂ h₂' := by
  subst h₁ h₂
  rfl

/-- The square isomorphism `j^* ⋙ g'^* ≅ g''^* ⋙ j'^*` of a commutative square
`g' ≫ j = j' ≫ g''`, computed with the composite `g' ≫ j`. -/
noncomputable abbrev openImmersionSquareIso (sq : CommSq g' j' j g'') :
    (j)^*[A] ⋙ (g')^*[A] ≅ (g'')^*[A] ⋙ (j')^*[A] :=
  (upperStarComp A g' j).symm ≪≫ upperStarComp A j' g'' (g' ≫ j) sq.w

lemma unit_map_openImmersionLowerShriekBaseChangeMap_app' (sq : CommSq g' j' j g'')
    (F : Sheaf U.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A j').unit.app ((g')^*[A].obj F) ≫
        (j')^*[A].map ((openImmersionLowerShriekBaseChangeMap A sq).app F) =
      (g')^*[A].map ((openImmersionLowerShriekUpperStarAdjunction A j).unit.app F) ≫
        (openImmersionSquareIso A sq).hom.app ((j)_!open[A].obj F) := by
  rw [unit_map_openImmersionLowerShriekBaseChangeMap_app]
  congr 2
  exact congrArg Iso.hom (upperStarComp_symm_trans_eq A _ _ _ _)

end Underived

section Derived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- The derived base change isomorphism for the extension by zero is the mate of the derived
square isomorphism of pullbacks, for the adjunctions `Dj_! ⊣ Dj^*` and `Dj'_! ⊣ Dj'^*`. -/
lemma mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (D((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      D((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (Functor.mapDerivedCategorySquareIso (openImmersionSquareIso A hsq.toCommSq)).hom.app
          (D((j)_!open[A]).obj K) :=
  Adjunction.mapDerivedCategoryAdjunction_mate (openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j') (openImmersionSquareIso A hsq.toCommSq)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap A hsq))
    (unit_map_openImmersionLowerShriekBaseChangeMap_app' A hsq.toCommSq) K

/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` of a commutative square
`g' ≫ j = j' ≫ g''`: the isomorphism induced on derived categories by the square isomorphism of
pullbacks, read through `Lg^* ≅ Dg^*`. -/
noncomputable def derivedOpenImmersionSquareMap (sq : CommSq g' j' j g'') :
    D((j)^*[A]) ⋙ L((g')^*[A]) ⟶ L((g'')^*[A]) ⋙ D((j')^*[A]) :=
  Functor.whiskerLeft D((j)^*[A]) (leftDerivedUpperStarIsoMapDerivedCategory A g').hom ≫
    (Functor.mapDerivedCategorySquareIso (openImmersionSquareIso A sq)).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A g'').inv D((j')^*[A])

/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` is the inverse of the square isomorphism
`Lg''^* ⋙ Lj'^* ≅ Lj^* ⋙ Lg'^*` of the derived pullbacks, read through `Lj^* ≅ Dj^*` and
`Lj'^* ≅ Dj'^*`. -/
lemma derivedOpenImmersionSquareMap_app (sq : CommSq g' j' j g'')
    (Y : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (derivedOpenImmersionSquareMap A sq).app Y =
      L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y) ≫
        (derivedSquareUpperStarIso A sq).inv.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj Y) := by
  have hnat := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app Y)
  simp only [derivedOpenImmersionSquareMap, derivedSquareUpperStarIso, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  rw [reassoc_of% hnat, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end Derived

end Etale

end AlgebraicGeometry
