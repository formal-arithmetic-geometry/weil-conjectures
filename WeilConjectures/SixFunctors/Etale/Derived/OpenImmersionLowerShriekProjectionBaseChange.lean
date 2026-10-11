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

/-- The derived base change isomorphism for the extension by zero is the mate of the square map
`derivedOpenImmersionSquareMap`. -/
lemma unit_map_derivedOpenImmersionLowerShriekBaseChangeIso (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app (L((g')^*[A]).obj K) ≫
        D((j')^*[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K) =
      L((g')^*[A]).map ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) ≫
        (derivedOpenImmersionSquareMap A hsq.toCommSq).app (D((j)_!open[A]).obj K) := by
  have h₁ := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app K)
  have h₂ := (leftDerivedUpperStarIsoMapDerivedCategory A g').hom.naturality
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K)
  dsimp at h₁ h₂
  simp only [derivedOpenImmersionLowerShriekBaseChangeIso, derivedOpenImmersionSquareMap,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp]
  rw [← reassoc_of% h₁, reassoc_of% (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate
    A hsq K), reassoc_of% h₂]
  rfl

variable [Etale.UpperStarPreservesFlat A]

set_option maxHeartbeats 1000000 in
/-- The square map `Dj^* ⋙ Lg'^* ⟶ Lg''^* ⋙ Dj'^*` and the square isomorphism of the derived
pullbacks are compatible with the comparisons `Dj^*X ⊗ᴸ Lj^*Y ≅ Dj^*(X ⊗ᴸ Y)` and the tensor
comparisons of the derived pullbacks. -/
lemma derivedOpenImmersionSquareMap_tensor (sq : CommSq g' j' j g'')
    (X Y : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    L((g')^*[A]).map (((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app X).app Y) ≫
        (derivedOpenImmersionSquareMap A sq).app (((-⊗ᴸ-(Z)[A]).obj X).obj Y) ≫
        D((j')^*[A]).map (((leftDerivedUpperStarTensorComparison A g'').app X).app Y) =
      ((leftDerivedUpperStarTensorComparison A g').app (D((j)^*[A]).obj X)).app
          (L((j)^*[A]).obj Y) ≫
        ((-⊗ᴸ-(U')[A]).map ((derivedOpenImmersionSquareMap A sq).app X)).app _ ≫
        ((-⊗ᴸ-(U')[A]).obj _).map ((derivedSquareUpperStarIso A sq).inv.app Y) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j').hom.app
          (L((g'')^*[A]).obj X)).app (L((g'')^*[A]).obj Y) := by
  rw [derivedOpenImmersionSquareMap_app, derivedOpenImmersionSquareMap_app]
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.postcompose₂_map_app_app_app, Functor.map_comp, Category.assoc]
  have key₀ : L((g')^*[A]).map ((leftDerivedUpperStarTensorIso A j X Y).inv) ≫
      (derivedSquareUpperStarIso A sq).inv.app (((-⊗ᴸ-(Z)[A]).obj X).obj Y) ≫
      L((j')^*[A]).map (((leftDerivedUpperStarTensorComparison A g'').app X).app Y) =
      ((leftDerivedUpperStarTensorComparison A g').app (L((j)^*[A]).obj X)).app
          (L((j)^*[A]).obj Y) ≫
        ((derivedSquareUpperStarIso A sq).inv.app X ⊗ₘ (derivedSquareUpperStarIso A sq).inv.app Y) ≫
        (leftDerivedUpperStarTensorIso A j' (L((g'')^*[A]).obj X) (L((g'')^*[A]).obj Y)).inv := by
    have h := derivedSquareUpperStarIso_hom_tensor A sq X Y
    rw [← cancel_epi (L((g')^*[A]).map (leftDerivedUpperStarTensorIso A j X Y).hom),
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv, ← cancel_mono ((derivedSquareUpperStarIso A sq).hom.app X ⊗ₘ
      (derivedSquareUpperStarIso A sq).hom.app Y)]
    simp only [Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
      leftDerivedUpperStarTensorIso_hom]
    rw [h]
    erw [Iso.inv_hom_id_app_assoc]
    erw [id_tensorHom_id, Category.comp_id]
  have c₁ : L((g')^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app
      (((-⊗ᴸ-(Z)[A]).obj X).obj Y)) ≫ L((g')^*[A]).map
        ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app (((-⊗ᴸ-(Z)[A]).obj X).obj Y)) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have c₂ := (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.naturality
    (((leftDerivedUpperStarTensorComparison A g'').app X).app Y)
  rw [reassoc_of% c₁]
  erw [← c₂]
  erw [reassoc_of% key₀]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map]
  have n₁ := leftDerivedUpperStarTensorComparison_naturality A g'
    ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app X) (𝟙 (L((j)^*[A]).obj Y))
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at n₁
  rw [reassoc_of% n₁]
  have w : (leftDerivedUpperStarIsoMapDerivedCategory A j').hom.app (L((g'')^*[A]).obj X) ▷
      L((g')^*[A]).obj (L((j)^*[A]).obj Y) ≫
      D((j')^*[A]).obj (L((g'')^*[A]).obj X) ◁ (derivedSquareUpperStarIso A sq).inv.app Y ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A j').inv.app (L((g'')^*[A]).obj X) ▷
        L((j')^*[A]).obj (L((g'')^*[A]).obj Y) =
      L((j')^*[A]).obj (L((g'')^*[A]).obj X) ◁ (derivedSquareUpperStarIso A sq).inv.app Y := by
    rw [← whisker_exchange_assoc]
    erw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight, Category.comp_id]
  erw [reassoc_of% w]
  rw [tensorHom_def, Category.assoc]
  rfl

/-- **The projection formula for the extension by zero commutes with base change**: for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, `K` in `D(U_ét)` and `M` in
`D(Z_ét)`, the square
```
Dj'_!Lg'^*(K ⊗ᴸ Lj^*M) ──≅──▶ Lg''^*Dj_!(K ⊗ᴸ Lj^*M) ──Lg''^* π──▶ Lg''^*(Dj_!K ⊗ᴸ M)
          │                                                              │
          ▼                                                              ▼
Dj'_!(Lg'^*K ⊗ᴸ Lj'^*Lg''^*M) ──π──▶ Dj'_!Lg'^*K ⊗ᴸ Lg''^*M ──≅ ⊗ 1──▶ Lg''^*Dj_!K ⊗ᴸ Lg''^*M
```
commutes, where `π` is the projection map, the horizontal isomorphisms are the base change
isomorphism, and the vertical arrows are the tensor comparisons of the derived pullbacks
followed, on the left, by `Lg'^*Lj^* ≅ Lj'^*Lg''^*`. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_baseChange (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app
          (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M)) ≫
        L((g'')^*[A]).map (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A g'').app (D((j)_!open[A]).obj K)).app M =
      D((j')_!open[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((j)^*[A]).obj M)) ≫
        D((j')_!open[A]).map (((-⊗ᴸ-(U')[A]).obj (L((g')^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A hsq.toCommSq).inv.app M)) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j').app (L((g')^*[A]).obj K)).app
          (L((g'')^*[A]).obj M) ≫
        ((-⊗ᴸ-(Z')[A]).map ((derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K)).app
          (L((g'')^*[A]).obj M) :=
  Adjunction.projectionMap_mate (derivedOpenImmersionLowerShriekUpperStarAdjunction A j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j') L((j)^*[A]) L((j')^*[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso A j').hom
    (leftDerivedUpperStarTensorComparison A g') (leftDerivedUpperStarTensorComparison A g'')
    (derivedOpenImmersionSquareMap A hsq.toCommSq) (derivedSquareUpperStarIso A hsq.toCommSq).inv
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom
    (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso A hsq)
    (derivedOpenImmersionSquareMap_tensor A hsq.toCommSq) K M

end Derived

end Etale

end AlgebraicGeometry
