/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Base change for unbounded right derived functors

Consider a square of additive functors between abelian categories
```
    B ───── G ─────▶ C
    │                │
    β                γ
    ▼                ▼
    B' ──── G' ────▶ C'
```
related by a natural transformation `e : G ⋙ γ ⟶ β ⋙ G'`, where `β` and `γ` are exact and `B`,
`B'` have K-injective resolutions. We construct the base change morphism
`RG ⋙ D(γ) ⟶ D(β) ⋙ RG'` of functors `DerivedCategory B ⥤ DerivedCategory C'`
(`CategoryTheory.Functor.rightDerivedFunctorBaseChange`): it is the unique morphism compatible
with the units, i.e. on a complex `K` it is `e : γ G(K) ⟶ G' β(K)` followed by the unit
`G' β(K) ⟶ RG'(β K)` (`CategoryTheory.Functor.rightDerivedFunctorBaseChange_app_fac`).

This is the unbounded analogue of `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange`.
Its component at `K` is an isomorphism as soon as `K` is K-injective and the unit of `RG'` is an
isomorphism at `β K` (`CategoryTheory.Functor.isIso_rightDerivedFunctorBaseChange_app`).
-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Functor

/-- For an additive functor `F : B ⥤ C`, the right derived functor `RF` followed by any functor
`T : DerivedCategory C ⥤ E` is a right derived functor of `F ⋙ T`: right derived functors computed
by K-injective resolutions are absolute. -/
instance isRightDerivedFunctor_rightDerivedFunctor_whiskerRight {B C E : Type*} [Category* B]
    [Category* C] [Category* E] [Abelian B] [Abelian C] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasKInjectiveResolutions B] (F : B ⥤ C) [F.Additive]
    (T : DerivedCategory C ⥤ E) :
    (F.rightDerivedFunctor ⋙ T).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorUnit T ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso B (.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism B)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

section SquareIso

variable {A B₁ B₂ E : Type*} [Category* A] [Category* B₁] [Category* B₂] [Category* E]
  [Abelian A] [Abelian B₁] [Abelian B₂] [Abelian E] [HasDerivedCategory A]
  [HasDerivedCategory B₁] [HasDerivedCategory B₂] [HasDerivedCategory E]
  {F₁ : A ⥤ B₁} {F₂ : B₁ ⥤ E} {G₁ : A ⥤ B₂} {G₂ : B₂ ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- On the image `Qh X` of an object of the homotopy category, the inverse of the isomorphism
`D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by `e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` is the image of the morphism
induced by `e.inv` on homotopy categories. -/
lemma mapDerivedCategorySquareIso_inv_app_Qh_obj (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (X : HomotopyCategory A (.up ℤ)) :
    G₂.mapDerivedCategoryFactorsh.inv.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.inv.app X) ≫
        (mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app X) ≫
        F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app X) := by
  have h := mapDerivedCategorySquareIso_hom_app_Qh_obj e.symm X
  simp only [mapHomotopyCategoryCompIso_refl_hom_app, mapHomotopyCategoryCompIso_refl_inv_app,
    Category.id_comp, Category.comp_id, Iso.symm_hom] at h
  rw [← cancel_mono (F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app X) ≫
    F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X))]
  have hi : (mapDerivedCategorySquareIso e).inv = (mapDerivedCategorySquareIso e.symm).hom := by
    simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc]
    rfl
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rw [hi]
  exact h

end SquareIso

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [HasKInjectiveResolutions B] [HasKInjectiveResolutions B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The base change morphism `G(K) ⟶ RG'(β K)` at the level of homotopy categories, from which
`Functor.rightDerivedFunctorBaseChange` is obtained by the universal property of `RG`: it is
`γ G(K) ⟶ G' β(K)` followed by the unit of `RG'`. -/
noncomputable def rightDerivedFunctorBaseChangeAux (e : G ⋙ γ ⟶ β ⋙ G') :
    G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ γ.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ β.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) γ.mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ γ)) (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e (.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (β ⋙ G')) (.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (β.mapHomotopyCategory (.up ℤ)) G'.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight β.mapDerivedCategoryFactorsh.inv G'.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- The base change morphism `RG ⋙ D(γ) ⟶ D(β) ⋙ RG'` attached to a natural transformation
`e : G ⋙ γ ⟶ β ⋙ G'` with `β` and `γ` exact. -/
noncomputable def rightDerivedFunctorBaseChange (e : G ⋙ γ ⟶ β ⋙ G') :
    G.rightDerivedFunctor ⋙ γ.mapDerivedCategory ⟶
      β.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  (G.rightDerivedFunctor ⋙ γ.mapDerivedCategory).rightDerivedDesc
    (Functor.whiskerRight G.rightDerivedFunctorUnit γ.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso B (.up ℤ)) _ (rightDerivedFunctorBaseChangeAux e)

/-- The base change morphism is characterized by its compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorBaseChange_fac (e : G ⋙ γ ⟶ β ⋙ G') :
    (Functor.whiskerRight G.rightDerivedFunctorUnit γ.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft DerivedCategory.Qh (rightDerivedFunctorBaseChange e) =
    rightDerivedFunctorBaseChangeAux e :=
  Functor.rightDerived_fac _ _ _ _ (rightDerivedFunctorBaseChangeAux e)

/-- The componentwise form of `Functor.rightDerivedFunctorBaseChange_fac`: on an object `K` of the
homotopy category, the base change morphism precomposed with the unit `G(K) ⟶ RG(K)` is
`e : γ G(K) ⟶ G' β(K)` followed by the unit `G' β(K) ⟶ RG'(β K)`. -/
lemma rightDerivedFunctorBaseChange_app_fac (e : G ⋙ γ ⟶ β ⋙ G')
    (K : HomotopyCategory B (.up ℤ)) :
    γ.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        γ.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app K) ≫
        (rightDerivedFunctorBaseChange e).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K) ≫
        G'.rightDerivedFunctorUnit.app ((β.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G'.rightDerivedFunctor.map (β.mapDerivedCategoryFactorsh.inv.app K) := by
  have h := congr_app (rightDerivedFunctorBaseChange_fac e) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at h
  have hh := congrArg (fun k ↦
    γ.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫ k) h
  simp only [rightDerivedFunctorBaseChangeAux, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    mapHomotopyCategoryCompIso_refl_inv_app, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id_app_assoc] at hh
  erw [Category.id_comp, Category.id_comp] at hh
  exact hh

/-- The base change morphism is an isomorphism at a K-injective complex `K` as soon as `e` is an
isomorphism and the unit of `RG'` is an isomorphism at `β K`. -/
lemma isIso_rightDerivedFunctorBaseChange_app (e : G ⋙ γ ≅ β ⋙ G') (K : CochainComplex B ℤ)
    [K.IsKInjective]
    (hK : IsIso (G'.rightDerivedFunctorUnit.app
      ((β.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)))) :
    IsIso ((rightDerivedFunctorBaseChange e.hom).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  have h := rightDerivedFunctorBaseChange_app_fac e.hom ((HomotopyCategory.quotient _ _).obj K)
  let eh : (G ⋙ γ).mapHomotopyCategory (.up ℤ) ≅ (β ⋙ G').mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom _
      inv := NatTrans.mapHomotopyCategory e.inv _
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  have : IsIso ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ _).obj K)) :=
    inferInstanceAs (IsIso (eh.app _).hom)
  have : IsIso (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
      ((HomotopyCategory.quotient _ _).obj K)) ≫
        G'.rightDerivedFunctorUnit.app ((β.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj K)) ≫
        G'.rightDerivedFunctor.map (β.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K))) := inferInstance
  rw [← h] at this
  set P := (HomotopyCategory.quotient _ _).obj K
  have := IsIso.of_isIso_comp_left
    (γ.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj P))
    (γ.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app P) ≫
      (rightDerivedFunctorBaseChange e.hom).app (DerivedCategory.Qh.obj P))
  exact IsIso.of_isIso_comp_left (γ.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app P)) _


end CategoryTheory.Functor
