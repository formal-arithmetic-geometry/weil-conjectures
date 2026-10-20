/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.CategoryTheory.RightDerivedSingleH0
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Normalization of a derived counit on single objects

Source: Stacks Project, Tag 07A6.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A counit computed on complexes has the usual single-object normalization.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-right-derived-single-counit).

Proof: precompose the complex counit formula by the image of the canonical
single-complex comparison for R. Move that comparison across the localization
factorization for L. The resulting map of complexes is the ordinary counit in
degree zero and is zero elsewhere, by the termwise adjunction formula. -/
private theorem single_rightDerived_counit_of_formula (a : L ⊣ R)
    (a' : L.mapDerivedCategory ⊣ R.rightDerivedFunctor)
    (hc : ∀ K : CochainComplex D ℤ,
      L.mapDerivedCategory.map
          (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj K)) ≫
        a'.counit.app (DerivedCategory.Q.obj K) =
      L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) (X : D) :
    L.mapDerivedCategory.map (R.singleRightDerivedUnit.app X) ≫
        a'.counit.app ((DerivedCategory.singleFunctor D 0).obj X) =
      (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) ≫
        (DerivedCategory.singleFunctor D 0).map (a.counit.app X) := by
  let K := (HomologicalComplex.single D (.up ℤ) 0).obj X
  let b := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app X
  have hb : (L.mapHomologicalComplex (.up ℤ)).map b ≫
      (a.mapHomologicalComplex (.up ℤ)).counit.app K =
    (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app (R.obj X) ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (a.counit.app X) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [b, K, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        mapHomologicalComplex_counit_app_f]
      erw [HomologicalComplex.single_map_f_self]
      simp only [HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom, eqToIso.inv, eqToHom_refl]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
    · exact (L.map_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).eq_of_src _ _
  change L.mapDerivedCategory.map (DerivedCategory.Q.map b ≫ _) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  erw [hc K, L.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp, hb, DerivedCategory.Q.map_comp]
  have hs : (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) =
      L.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj (R.obj X)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app (R.obj X)) := by
    simp only [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      Functor.isoWhiskerLeft_inv, Iso.refl_inv,
      Category.id_comp]
    erw [Category.id_comp, Category.comp_id]
    rfl
  rw [hs, Category.assoc]
  rfl

section Canonical

open MonoidalCategory Abelian
variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived counit is the ordinary counit on the augmentation of a
single complex. Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-right-derived-single-counit).

Proof: the defining counit factorization of the derived adjunction, followed by
the exact-left-functor identification, gives the ordinary complex counit after
the right-derived unit. Apply this to a single complex and use its degreewise
counit calculation. No exactness of the right adjoint is required. -/
theorem single_rightDerived_counit (a : L ⊣ R) (X : D) :
    L.mapDerivedCategory.map (R.singleRightDerivedUnit.app X) ≫
        (a.derivedAdjunction.ofNatIsoLeft
          L.leftDerivedFunctorIsoMapDerivedCategory).counit.app
            ((DerivedCategory.singleFunctor D 0).obj X) =
      (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) ≫
        (DerivedCategory.singleFunctor D 0).map (a.counit.app X) := by
  apply single_rightDerived_counit_of_formula a _ _ X
  intro K
  let K' := (HomotopyCategory.quotient D (.up ℤ)).obj K
  have h₁ := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit K'
  have h₂ := NatTrans.congr_app L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((R.mapHomotopyCategory (.up ℤ)).obj K')
  have h₄ := L.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (R.rightDerivedFunctorUnit.app K')
  simp only [ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [reassoc_of% h₄]
  change L.leftDerivedFunctorIsoMapDerivedCategory.inv.app _ ≫
    (L.leftDerivedFunctor.map (R.rightDerivedFunctorUnit.app K') ≫
      ((a.mapHomotopyCategory (.up ℤ)).derivedε
        (HomotopyCategory.quasiIso D (.up ℤ)) L.leftDerivedFunctorCounit
          R.rightDerivedFunctorUnit).app (DerivedCategory.Qh.obj K')) = _
  rw [h₁]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₂
  rw [← reassoc_of% h₂]
  simp only [Functor.comp_obj]
  erw [Iso.inv_hom_id_app_assoc]
  dsimp only [K']
  rw [mapHomotopyCategory_counit_app_quotient]
  change L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).counit.app K)) = _
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hq (Y : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).hom.app Y = 𝟙 _ := rfl
  have hqi (Y : CochainComplex D ℤ) :
      (DerivedCategory.quotientCompQhIso D).inv.app Y = 𝟙 _ := rfl
  simp only [hq, hqi, Functor.comp_obj]
  erw [Functor.map_id, Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact-right-functor specialization uses the termwise single comparison.
Source: Stacks Project, Tag 07A6.
(blueprint: lem-kun-right-derived-single-counit).

Proof: the right-derived uniqueness factorization identifies the single-object
augmentation followed by the exact-right-derived comparison with the inverse
termwise single comparison. Cancel this comparison in the transported counit
and apply `single_rightDerived_counit`. -/
theorem single_mapDerivedCategory_counit [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (a : L ⊣ R) (X : D) :
    L.mapDerivedCategory.map ((R.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
        a.mapDerivedCategoryAdjunction.counit.app
          ((DerivedCategory.singleFunctor D 0).obj X) =
      (L.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X) ≫
        (DerivedCategory.singleFunctor D 0).map (a.counit.app X) := by
  have hu : R.singleRightDerivedUnit.app X ≫
      R.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.singleFunctor D 0).obj X) =
      (R.mapDerivedCategorySingleFunctor 0).inv.app X := by
    dsimp only [Functor.singleRightDerivedUnit, NatTrans.app]
    rw [Category.assoc]
    have hf := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((HomotopyCategory.singleFunctor D 0).obj X)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [hf]
    have hh : R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.singleFunctor D 0).obj X) =
        R.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor D 0).obj X) := by
      change R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((CochainComplex.singleFunctor D 0).obj X)) = _
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
      have hq (Y : CochainComplex D ℤ) :
          (DerivedCategory.quotientCompQhIso D).hom.app Y = 𝟙 _ := rfl
      have hqi (Y : CochainComplex C ℤ) :
          (DerivedCategory.quotientCompQhIso C).inv.app Y = 𝟙 _ := rfl
      simp only [hq, hqi, Functor.comp_obj]
      erw [Functor.map_id, Functor.map_id]
      simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono (R.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.singleFunctor D 0).obj X))).1
    rw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [hh]
    exact (R.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X).symm
  rw [← hu]
  simp only [mapDerivedCategoryAdjunction, ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  erw [← L.mapDerivedCategory.map_comp_assoc
    (R.rightDerivedFunctorIsoMapDerivedCategory.hom.app
      ((DerivedCategory.singleFunctor D 0).obj X))
    (R.rightDerivedFunctorIsoMapDerivedCategory.inv.app
      ((DerivedCategory.singleFunctor D 0).obj X)), Iso.hom_inv_id_app]
  erw [L.mapDerivedCategory.map_id, Category.id_comp]
  exact single_rightDerived_counit a X

end Canonical
end CategoryTheory.Adjunction
