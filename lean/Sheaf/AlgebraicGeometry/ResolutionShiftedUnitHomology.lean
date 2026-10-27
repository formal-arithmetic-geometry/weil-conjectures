/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.AlgebraicGeometry.ResolutionCocycleHomologyTail
import WeilConjectures.CategoryTheory.CanonicalResolutionHomologyComparison

/-! # Homology of the derived unit on a shifted resolution

Source: Stacks Project, Tags 072W and 0DVC.
(blueprint: lem-weil-pbc-resolution-shifted-unit-homology).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

section ShiftComparison

private noncomputable instance quotientShift {C : Type*} [Category C] [Abelian C] :
    (HomotopyCategory.Plus.quotient C).CommShift ℤ :=
  Functor.CommShift.ofComp (HomotopyCategory.Plus.quotientCompιIso C) ℤ

private noncomputable instance qShift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] : (DerivedCategory.Plus.Q (C := C)).CommShift ℤ := by
  dsimp only [DerivedCategory.Plus.Q]
  infer_instance

private noncomputable instance mapShift {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (R : A ⥤ B) [R.Additive] :
    R.mapCochainComplexPlus.CommShift ℤ :=
  Functor.CommShift.ofComp R.mapCochainComplexPlusCompι ℤ

private instance quotientShiftCompat {C : Type*} [Category C] [Abelian C] :
    NatTrans.CommShift (HomotopyCategory.Plus.quotientCompιIso C).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

private instance mapShiftCompat {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (R : A ⥤ B) [R.Additive] :
    NatTrans.CommShift R.mapCochainComplexPlusCompι.hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
  (R : A ⥤ B) [R.Additive]

private noncomputable def mappedQuotientAmbient :
    (HomotopyCategory.Plus.quotient A ⋙ R.mapHomotopyCategoryPlus) ⋙
        HomotopyCategory.Plus.ι B ≅
      (R.mapCochainComplexPlus ⋙ HomotopyCategory.Plus.quotient B) ⋙
        HomotopyCategory.Plus.ι B :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((HomotopyCategory.plus B).liftCompιIso
      (HomotopyCategory.Plus.ι A ⋙ R.mapHomotopyCategory (.up ℤ)) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (R.mapHomotopyCategoryFactors (.up ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight R.mapCochainComplexPlusCompι.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (HomotopyCategory.Plus.quotientCompιIso B).symm ≪≫
    (Functor.associator _ _ _).symm

private noncomputable def mappedQuotient :
    HomotopyCategory.Plus.quotient A ⋙ R.mapHomotopyCategoryPlus ≅
      R.mapCochainComplexPlus ⋙ HomotopyCategory.Plus.quotient B :=
  Functor.fullyFaithfulCancelRight (HomotopyCategory.Plus.ι B) (mappedQuotientAmbient R)

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem mappedQuotient_hom_app (K : CochainComplex.Plus A) :
    (mappedQuotient R).hom.app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι B).map_injective
  change (HomotopyCategory.Plus.ι B).map
    ((HomotopyCategory.Plus.ι B).preimage ((mappedQuotientAmbient R).hom.app K)) = _
  rw [Functor.map_preimage]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, mappedQuotientAmbient,
    ObjectProperty.liftCompιIso, HomotopyCategory.Plus.quotientCompιIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift,
    Functor.mapCochainComplexPlusCompι, Iso.refl_symm, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.refl_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Iso.refl_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.Plus.quotient_obj_obj_as, Functor.whiskerLeft_app,
    NatTrans.id_app, ObjectProperty.lift_obj_obj, Functor.associator_inv_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Category.comp_id,
    Category.id_comp, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

private instance mappedQuotientShift : NatTrans.CommShift (mappedQuotient R).hom ℤ := by
  have he : Functor.whiskerRight (mappedQuotient R).hom (HomotopyCategory.Plus.ι B) =
      (mappedQuotientAmbient R).hom := by
    ext K
    change (HomotopyCategory.Plus.ι B).map
      ((HomotopyCategory.Plus.ι B).preimage ((mappedQuotientAmbient R).hom.app K)) = _
    exact Functor.map_preimage _ _
  have : NatTrans.CommShift
      (Functor.whiskerRight (mappedQuotient R).hom (HomotopyCategory.Plus.ι B)) ℤ := by
    rw [he]
    unfold mappedQuotientAmbient
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι B)

-- Keep the associators explicit: shift compatibility depends on the parenthesization.
private noncomputable def complexUnit :
    R.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙ R.rightDerivedFunctorPlus :=
  (Functor.associator R.mapCochainComplexPlus (HomotopyCategory.Plus.quotient B)
      DerivedCategory.Plus.Qh).inv ≫
    (Functor.isoWhiskerRight (mappedQuotient R).symm DerivedCategory.Plus.Qh).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.quotient A) R.rightDerivedFunctorPlusUnit ≫
    (Functor.associator (HomotopyCategory.Plus.quotient A)
      DerivedCategory.Plus.Qh R.rightDerivedFunctorPlus).inv

private theorem complexUnit_app (K : CochainComplex.Plus A) :
    (complexUnit R).app K =
      R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj K) := by
  have hi : (mappedQuotient R).inv.app K = 𝟙 _ :=
    congrArg Iso.inv (Iso.ext (mappedQuotient_hom_app R K) :
      (mappedQuotient R).app K = Iso.refl _)
  simp only [complexUnit, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, hi, CategoryTheory.Functor.map_id,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]

private instance complexUnitShift : NatTrans.CommShift (complexUnit R) ℤ := by
  have : NatTrans.CommShift (mappedQuotient R).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  unfold complexUnit
  simp only [Functor.isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

private noncomputable def quotientDerivedAmbient {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι C ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.TStructure.t.plus.liftCompιIso
      (HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh) _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso C) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C)

private theorem quotientDerivedAmbient_hom_app {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) :
    (quotientDerivedAmbient (C := C)).hom.app K = 𝟙 _ := by
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, quotientDerivedAmbient,
    ObjectProperty.liftCompιIso, HomotopyCategory.Plus.quotientCompιIso,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, NatTrans.id_app, ObjectProperty.lift_obj_obj,
    Functor.associator_inv_app, Functor.whiskerRight_app, Quotient.lift.isLift_hom,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

private instance quotientDerivedAmbientShift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] :
    NatTrans.CommShift (quotientDerivedAmbient (C := C)).hom ℤ := by
  unfold quotientDerivedAmbient
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom]
  infer_instance

private theorem quotient_shift_inclusion {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) (n : ℤ) :
    DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Q.map ((CochainComplex.Plus.ι C).commShiftIso n |>.hom.app K) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app K.obj := by
  have h := NatTrans.shift_app_comm (quotientDerivedAmbient (C := C)).hom n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    quotientDerivedAmbient_hom_app, Category.id_comp] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

private theorem quotient_shift_comparison {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K J : CochainComplex.Plus C) (n : ℤ) (b : J ≅ K⟦n⟧) :
    DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Q.map b.hom ≫
          (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫
      (DerivedCategory.Plus.ι.commShiftIso n).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Q.map
        (b.hom.hom ≫ ((CochainComplex.Plus.ι C).commShiftIso n).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app K.obj := by
  rw [Functor.map_comp, Category.assoc, quotient_shift_inclusion]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem quotient_homology_comparison {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctorObjQIso K n).hom =
      (DerivedCategory.homologyFunctorFactors C n).hom.app K.obj := by
  simp only [DerivedCategory.Plus.homologyFunctorObjQIso, Iso.trans_hom,
    Iso.app_hom]
  erw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  have he : (DerivedCategory.quotientCompQhIso C).hom.app K.obj = 𝟙 _ := rfl
  erw [he, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id, Category.id_comp]
  rfl

private theorem quotient_homology_comparison_inv {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex.Plus C) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactors C n).inv.app K.obj =
      (DerivedCategory.Plus.homologyFunctorObjQIso K n).inv := by
  exact (congrArg Iso.inv (Iso.ext (quotient_homology_comparison K n) :
    DerivedCategory.Plus.homologyFunctorObjQIso K n =
      (DerivedCategory.homologyFunctorFactors C n).app K.obj)).symm

-- Compare the bounded-below quotient through its fully faithful ambient inclusion.
private theorem quotient_homology_shift {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K J : CochainComplex.Plus C) (n : ℤ) (b : J ≅ K⟦n⟧) :
    (DerivedCategory.Plus.homologyFunctorObjQIso J 0).inv ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map
        (DerivedCategory.Plus.Q.map b.hom ≫
          (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n 0 n (add_zero _)).hom.app
        (DerivedCategory.Plus.Q.obj K) =
    HomologicalComplex.homologyMap
        (b.hom.hom ≫ ((CochainComplex.Plus.ι C).commShiftIso n).hom.app K) 0 ≫
      ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso n 0 n
        (add_zero _)).hom.app K.obj ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso K n).inv := by
  have hs : ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso n 0 n
      (add_zero _)).hom.app (DerivedCategory.Plus.Q.obj K) =
      (DerivedCategory.homologyFunctor C 0).map
        ((DerivedCategory.Plus.ι.commShiftIso n).hom.app (DerivedCategory.Plus.Q.obj K)) ≫
      ((DerivedCategory.homologyFunctor C 0).shiftIso n 0 n (add_zero _)).hom.app
        (DerivedCategory.Q.obj K.obj) := by
    refine (Category.id_comp _).trans ?_
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rfl
  rw [hs]
  change (DerivedCategory.Plus.homologyFunctorObjQIso J 0).inv ≫
    (DerivedCategory.homologyFunctor C 0).map
      (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map b.hom ≫
        (DerivedCategory.Plus.Q.commShiftIso n).hom.app K)) ≫
    (DerivedCategory.homologyFunctor C 0).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, quotient_shift_comparison]
  have h := DerivedCategory.shiftMap_homologyFunctor_map_Q
    (b.hom.hom ≫ ((CochainComplex.Plus.ι C).commShiftIso n).hom.app K) 0 n (add_zero _)
  simp only [Functor.shiftMap, ShiftedHom.map] at h
  erw [h]
  erw [← quotient_homology_comparison J 0, Iso.inv_hom_id_assoc]
  change (HomologicalComplex.homologyMap
    (b.hom.hom ≫ ((CochainComplex.Plus.ι C).commShiftIso n).hom.app K) 0 ≫
    ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso n 0 n
      (add_zero _)).hom.app K.obj) ≫
    (DerivedCategory.homologyFunctorFactors C n).inv.app K.obj = _
  rw [quotient_homology_comparison_inv, Category.assoc]

private theorem complex_unit_shift (K J : CochainComplex.Plus A) (n : ℤ)
    (b : J ≅ K⟦n⟧) :
    (complexUnit R).app J ≫
        R.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map b.hom ≫
            (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫
        (R.rightDerivedFunctorPlus.commShiftIso n).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          (R.mapCochainComplexPlus.map b.hom ≫
            (R.mapCochainComplexPlus.commShiftIso n).hom.app K) ≫
        (DerivedCategory.Plus.Q.commShiftIso n).hom.app
          (R.mapCochainComplexPlus.obj K) ≫
        ((complexUnit R).app K)⟦n⟧' := by
  have h := NatTrans.shift_app_comm (complexUnit R) n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] at h
  have hn := (complexUnit R).naturality b.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, ← h]

private theorem unit_homology_shift (K J : CochainComplex.Plus A) (n : ℤ)
    (b : J ≅ K⟦n⟧) (M : DerivedCategory.Plus A)
    (a : M ≅ DerivedCategory.Plus.Q.obj K)
    (alpha : M⟦n⟧ ≅ DerivedCategory.Plus.Q.obj J)
    (ha : alpha.inv = (DerivedCategory.Plus.Q.map b.hom ≫
      (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫ a.inv⟦n⟧') :
    let H := DerivedCategory.Plus.homologyFunctor B 0
    (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj J) 0).inv ≫
      H.map ((complexUnit R).app J) ≫ H.map (R.rightDerivedFunctorPlus.map alpha.inv) ≫
      H.map ((R.rightDerivedFunctorPlus.commShiftIso n).hom.app M) ≫
      (H.shiftIso n 0 n (add_zero _)).hom.app (R.rightDerivedFunctorPlus.obj M) =
    HomologicalComplex.homologyMap
        ((R.mapCochainComplexPlus.map b.hom ≫
          (R.mapCochainComplexPlus.commShiftIso n).hom.app K).hom ≫
          ((CochainComplex.Plus.ι B).commShiftIso n).hom.app
            (R.mapCochainComplexPlus.obj K)) 0 ≫
      ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso n 0 n
        (add_zero _)).hom.app (R.mapCochainComplexPlus.obj K).obj ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj K) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor B n).map
        ((complexUnit R).app K ≫ R.rightDerivedFunctorPlus.map a.inv) := by
  intro H
  let t := R.mapCochainComplexPlus.mapIso b ≪≫
    (R.mapCochainComplexPlus.commShiftIso n).app K
  let v := (complexUnit R).app K ≫ R.rightDerivedFunctorPlus.map a.inv
  have hd := complex_unit_shift R K J n b
  have hd' : (complexUnit R).app J ≫ R.rightDerivedFunctorPlus.map alpha.inv ≫
      (R.rightDerivedFunctorPlus.commShiftIso n).hom.app M =
    DerivedCategory.Plus.Q.map t.hom ≫
      (DerivedCategory.Plus.Q.commShiftIso n).hom.app
        (R.mapCochainComplexPlus.obj K) ≫ v⟦n⟧' := by
    rw [ha, Functor.map_comp, Category.assoc,
      R.rightDerivedFunctorPlus.commShiftIso_hom_naturality]
    simpa only [t, v, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ z ≫ (R.rightDerivedFunctorPlus.map a.inv)⟦n⟧') hd
  have hm := congrArg (fun z ↦
    (DerivedCategory.Plus.homologyFunctorObjQIso
      (R.mapCochainComplexPlus.obj J) 0).inv ≫ H.map z ≫
    (H.shiftIso n 0 n (add_zero _)).hom.app (R.rightDerivedFunctorPlus.obj M)) hd'
  simp only [Functor.map_comp, Category.assoc] at hm
  have hn : H.map (v⟦n⟧') ≫
      (H.shiftIso n 0 n (add_zero _)).hom.app (R.rightDerivedFunctorPlus.obj M) =
    (H.shiftIso n 0 n (add_zero _)).hom.app
        (DerivedCategory.Plus.Q.obj (R.mapCochainComplexPlus.obj K)) ≫
      (DerivedCategory.Plus.homologyFunctor B n).map v :=
    H.shiftIso_hom_naturality n 0 n (add_zero _) v
  erw [hn] at hm
  have hs := quotient_homology_shift (R.mapCochainComplexPlus.obj K)
    (R.mapCochainComplexPlus.obj J) n t
  rw [hm]
  simp only [Functor.map_comp, Category.assoc] at hs
  simpa only [t, v, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
    congrArg (fun z ↦ z ≫ (DerivedCategory.Plus.homologyFunctor B n).map v) hs

private theorem unit_homology_shift_native (K J : CochainComplex.Plus A) (n : ℤ)
    (b : J ≅ K⟦n⟧) (M : DerivedCategory.Plus A)
    (a : M ≅ DerivedCategory.Plus.Q.obj K)
    (alpha : M⟦n⟧ ≅ DerivedCategory.Plus.Q.obj J)
    (ha : alpha.inv = (DerivedCategory.Plus.Q.map b.hom ≫
      (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫ a.inv⟦n⟧') :
    let H := DerivedCategory.Plus.homologyFunctor B 0
    (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj J) 0).inv ≫
      H.map (R.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj J)) ≫
      H.map (R.rightDerivedFunctorPlus.map alpha.inv) ≫
      H.map ((R.rightDerivedFunctorPlus.commShiftIso n).hom.app M) ≫
      ((H.shiftIso n 0 n (add_zero _)).hom.app (R.rightDerivedFunctorPlus.obj M) :
        H.obj ((R.rightDerivedFunctorPlus.obj M)⟦n⟧) ⟶
          (DerivedCategory.Plus.homologyFunctor B n).obj (R.rightDerivedFunctorPlus.obj M)) =
    HomologicalComplex.homologyMap
        ((R.mapCochainComplexPlus.map b.hom ≫
          (R.mapCochainComplexPlus.commShiftIso n).hom.app K).hom ≫
          ((CochainComplex.Plus.ι B).commShiftIso n).hom.app
            (R.mapCochainComplexPlus.obj K)) 0 ≫
      ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso n 0 n
        (add_zero _)).hom.app (R.mapCochainComplexPlus.obj K).obj ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj K) n).inv ≫
      (DerivedCategory.Plus.homologyFunctor B n).map
        (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj K) ≫
          R.rightDerivedFunctorPlus.map a.inv) := by
  simpa only [complexUnit_app] using unit_homology_shift R K J n b M a alpha ha

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem mapped_shift_comparison (K J : CochainComplex.Plus A) (n : ℤ)
    (b : J ≅ K⟦n⟧) :
    (R.mapCochainComplexPlus.map b.hom ≫
        (R.mapCochainComplexPlus.commShiftIso n).hom.app K).hom ≫
      ((CochainComplex.Plus.ι B).commShiftIso n).hom.app (R.mapCochainComplexPlus.obj K) =
    (R.mapHomologicalComplex (.up ℤ)).map
        (b.hom.hom ≫ ((CochainComplex.Plus.ι A).commShiftIso n).hom.app K) ≫
      ((R.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app K.obj := by
  have h := NatTrans.shift_app_comm R.mapCochainComplexPlusCompι.hom n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Functor.mapCochainComplexPlusCompι, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  change ((R.mapHomologicalComplex (.up ℤ)).map b.hom.hom ≫
    (CochainComplex.Plus.ι B).map
      ((R.mapCochainComplexPlus.commShiftIso n).hom.app K)) ≫ _ = _
  rw [Category.assoc, h, ← Functor.map_comp_assoc]
  rfl

omit [EnoughInjectives A] in
private theorem augmentation_shift_factorization (K J : CochainComplex.Plus A) (n : ℤ)
    (b : J ≅ K⟦n⟧) (M : DerivedCategory.Plus A)
    (a : M ≅ DerivedCategory.Plus.Q.obj K)
    (alpha : M⟦n⟧ ≅ DerivedCategory.Plus.Q.obj J)
    (h : DerivedCategory.Plus.ι.map alpha.inv ≫
        (DerivedCategory.Plus.ι.commShiftIso n).hom.app M =
      DerivedCategory.Q.map
          (b.hom.hom ≫ ((CochainComplex.Plus.ι A).commShiftIso n).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K.obj ≫
        (DerivedCategory.Plus.ι.map a.inv)⟦n⟧') :
    alpha.inv = (DerivedCategory.Plus.Q.map b.hom ≫
      (DerivedCategory.Plus.Q.commShiftIso n).hom.app K) ≫ a.inv⟦n⟧' := by
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso n).hom.app M)).1
  rw [Functor.map_comp, Category.assoc,
    DerivedCategory.Plus.ι.commShiftIso_hom_naturality, ← Category.assoc]
  rw [quotient_shift_comparison, Category.assoc]
  exact h

end ShiftComparison

private theorem resolution_homology_forward
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] {F : A} (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor B q).map (resolutionDerivedIso R I).hom ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨(R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex, 0,
            inferInstance⟩ q).hom =
      (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).hom ≫
        (I.isoRightDerivedObjCochainComplex R q).hom := by
  let e := (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat R) ≪≫
    ((R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)
  apply (cancel_mono e.hom).1
  have h := resolution_homology_transport R F I q
  simp only [canonicalResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at h
  erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality_assoc] at h
  dsimp only [ObjectProperty.isoMk, ObjectProperty.homMk] at h
  simpa only [e,
    InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    HomologicalComplex.homologyFunctor_map, Category.assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id_assoc] using h.symm

private theorem resolution_homology_inverse
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] {F : A} (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩) q).inv ≫
      (DerivedCategory.Plus.homologyFunctor B q).map (resolutionDerivedIso R I).inv =
    (I.isoRightDerivedObjCochainComplex R q).inv ≫
      (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv := by
  have h : (DerivedCategory.Plus.homologyFunctor B q).mapIso
        (resolutionDerivedIso R I) ≪≫
      DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩) q =
    R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q ≪≫
      I.isoRightDerivedObjCochainComplex R q :=
    Iso.ext (resolution_homology_forward R I q)
  exact congrArg Iso.inv h

private theorem resolution_homology_inverse_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] {F : A} (I : InjectiveResolution F) (q : ℕ) :
    let L : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
    (DerivedCategory.Plus.homologyFunctorObjQIso (R.mapCochainComplexPlus.obj L) q).inv ≫
      (DerivedCategory.Plus.homologyFunctor B q).map
        (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj L) ≫
          R.rightDerivedFunctorPlus.map (resolutionAugmentationIso I).inv) =
    (I.isoRightDerivedObjCochainComplex R q).inv ≫
      (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv := by
  have h := resolution_homology_inverse R I q
  dsimp only [resolutionDerivedIso, Iso.trans_inv, Iso.symm_inv, asIso_hom,
    Functor.mapIso_inv] at h
  exact h

private theorem preimage_trans_cancel {C D : Type*} [Category C] [Category D]
    (U : C ⥤ D) [U.Full] [U.Faithful] {L J : C} {M N : D}
    (p : U.obj L ≅ M) (b : M ≅ N) (c : U.obj J ≅ N) :
    U.map (U.preimageIso (p ≪≫ b ≪≫ c.symm)).inv ≫ p.hom = c.hom ≫ b.inv := by
  simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv,
    Iso.symm_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem quotient_comparison_hom_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl

private theorem single_comparison_inv_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (F : C) (n : ℤ) :
    (DerivedCategory.singleFunctorIsoCompQ C n).inv.app F = 𝟙 _ := rfl

private theorem resolution_augmentation_inclusion {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {F : C} (I : InjectiveResolution F) :
    DerivedCategory.Plus.ι.map (resolutionAugmentationIso I).inv =
      (asIso (DerivedCategory.Q.map I.ι')).inv := by
  simp only [resolutionAugmentationIso, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_inv, Iso.symm_inv, Iso.app_inv]
  erw [quotient_comparison_hom_id, single_comparison_inv_id,
    Category.id_comp, Category.comp_id]

private noncomputable def shiftedResolution {A : Type*} [Category A] [Abelian A]
    {F : A} (I : InjectiveResolution F) (q : ℕ) : CochainComplex.Plus A :=
  ⟨I.cochainComplex⟦(q : ℤ)⟧, -(q : ℤ),
    I.cochainComplex.isStrictlyGE_shift 0 (q : ℤ) (-(q : ℤ)) (by simp)⟩

private noncomputable def shiftedAugmentation {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {F : A} (I : InjectiveResolution F) (q : ℕ) :
    ((DerivedCategory.Plus.singleFunctor A 0).obj F)⟦(q : ℤ)⟧ ≅
      DerivedCategory.Plus.Q.obj (shiftedResolution I q) :=
  DerivedCategory.Plus.ι.preimageIso
    (((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj F)) ≪≫
      (shiftFunctor _ (q : ℤ)).mapIso (asIso (DerivedCategory.Q.map I.ι')) ≪≫
      ((DerivedCategory.Q.commShiftIso (q : ℤ)).app I.cochainComplex).symm)

private theorem resolution_augmentation_ambient {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] {F : A} (q : ℕ) (I : InjectiveResolution F) :
    DerivedCategory.Plus.ι.map (shiftedAugmentation I q).inv ≫
      (DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) =
    (DerivedCategory.Q.commShiftIso (q : ℤ)).hom.app I.cochainComplex ≫
      (DerivedCategory.Plus.ι.map (resolutionAugmentationIso I).inv)⟦(q : ℤ)⟧' := by
  rw [resolution_augmentation_inclusion]
  exact preimage_trans_cancel DerivedCategory.Plus.ι
    (J := DerivedCategory.Plus.Q.obj (shiftedResolution I q))
    ((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    ((shiftFunctor _ (q : ℤ)).mapIso (asIso (DerivedCategory.Q.map I.ι')))
    ((DerivedCategory.Q.commShiftIso (q : ℤ)).app I.cochainComplex)

private theorem resolution_unit_homology_generic
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ B) [R.Additive] {F : A} (I : InjectiveResolution F) (q : ℕ)
    (J : CochainComplex.Plus A)
    (b : J ≅ (⟨I.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus A)⟦(q : ℤ)⟧)
    (alpha : ((DerivedCategory.Plus.singleFunctor A 0).obj F)⟦(q : ℤ)⟧ ≅
      DerivedCategory.Plus.Q.obj J)
    (ha : alpha.inv = (DerivedCategory.Plus.Q.map b.hom ≫
      (DerivedCategory.Plus.Q.commShiftIso (q : ℤ)).hom.app
        ⟨I.cochainComplex, 0, inferInstance⟩) ≫
      (resolutionAugmentationIso I).inv⟦(q : ℤ)⟧')
    (w : (R.mapHomologicalComplex (.up ℤ)).obj J.obj ⟶
      ((R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)⟦(q : ℤ)⟧)
    (hw : (R.mapCochainComplexPlus.map b.hom ≫
      (R.mapCochainComplexPlus.commShiftIso (q : ℤ)).hom.app
        ⟨I.cochainComplex, 0, inferInstance⟩).hom ≫
      ((CochainComplex.Plus.ι B).commShiftIso (q : ℤ)).hom.app
        (R.mapCochainComplexPlus.obj ⟨I.cochainComplex, 0, inferInstance⟩) = w) :
    let H := DerivedCategory.Plus.homologyFunctor B 0
    ∀ (sigma : H.obj (R.rightDerivedFunctorPlus.obj
          (((DerivedCategory.Plus.singleFunctor A 0).obj F)⟦(q : ℤ)⟧)) ≅
        (DerivedCategory.Plus.homologyFunctor B q).obj
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)))
      (_hsigma : sigma = H.mapIso ((R.rightDerivedFunctorPlus.commShiftIso (q : ℤ)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj F)) ≪≫
        (H.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).app
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)))
      (tail : ((R.mapHomologicalComplex (.up ℤ)).obj J.obj).homology 0 ⟶
        (DerivedCategory.Plus.homologyFunctor B q).obj
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)))
      (_htail : tail = HomologicalComplex.homologyMap w 0 ≫
          ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app
              ((R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≫
          (I.isoRightDerivedObjCochainComplex R q).inv ≫
          (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv),
    (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj J) 0).inv ≫
      H.map (R.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient A).obj J)) ≫
      H.map (R.rightDerivedFunctorPlus.map alpha.inv) ≫ sigma.hom = tail := by
  intro H sigma hsigma tail htail
  let L : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
  let a := resolutionAugmentationIso I
  let v := R.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.quotient A).obj L) ≫ R.rightDerivedFunctorPlus.map a.inv
  have hv : (DerivedCategory.Plus.homologyFunctorObjQIso
      (R.mapCochainComplexPlus.obj L) q).inv ≫
      (DerivedCategory.Plus.homologyFunctor B q).map v =
    (I.isoRightDerivedObjCochainComplex R q).inv ≫
      (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv :=
    resolution_homology_inverse_unit R I q
  have h := unit_homology_shift_native R L J (q : ℤ) b
    ((DerivedCategory.Plus.singleFunctor A 0).obj F) a alpha ha
  change (DerivedCategory.Plus.homologyFunctorObjQIso
      (R.mapCochainComplexPlus.obj J) 0).inv ≫
    H.map (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj J)) ≫
    H.map (R.rightDerivedFunctorPlus.map alpha.inv) ≫
    H.map ((R.rightDerivedFunctorPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj F)) ≫
    ((H.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app
      (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F)) :
      H.obj ((R.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj F))⟦(q : ℤ)⟧) ⟶
      (DerivedCategory.Plus.homologyFunctor B q).obj
        (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj F))) =
    _ at h
  rw [hw] at h
  change _ = HomologicalComplex.homologyMap w 0 ≫
    ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso
      (R.mapCochainComplexPlus.obj L) q).inv ≫
    (DerivedCategory.Plus.homologyFunctor B q).map v at h
  rw [hv] at h
  rw [hsigma, htail]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact h

private theorem resolution_unit_homology_aux
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A} (q : ℕ) (I : InjectiveResolution F) (R : A ⥤ B) [R.Additive] :
    let J := shiftedResolution I q
    let H := DerivedCategory.Plus.homologyFunctor B 0
    ∀ (sigma : H.obj (R.rightDerivedFunctorPlus.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)) ≅
        (DerivedCategory.Plus.homologyFunctor _ q).obj
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      (_hsigma : sigma = H.mapIso ((R.rightDerivedFunctorPlus.commShiftIso (q : ℤ)).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
        (H.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).app
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      (tail : ((R.mapHomologicalComplex (.up ℤ)).obj J.obj).homology 0 ⟶
        (DerivedCategory.Plus.homologyFunctor _ q).obj
          (R.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
      (_htail : tail =
        HomologicalComplex.homologyMap
            (((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app
              I.cochainComplex) 0 ≫
          ((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app
              ((R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≫
          (I.isoRightDerivedObjCochainComplex R q).inv ≫
          (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv),
    (DerivedCategory.Plus.homologyFunctorObjQIso
        (R.mapCochainComplexPlus.obj J) 0).inv ≫
      H.map (R.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj J)) ≫
      H.map (R.rightDerivedFunctorPlus.map (shiftedAugmentation I q).inv) ≫
      sigma.hom = tail := by
  intro J H sigma hsigma tail htail
  let L : CochainComplex.Plus A :=
    ⟨I.cochainComplex, 0, inferInstance⟩
  let a := resolutionAugmentationIso I
  let b : J ≅ L⟦(q : ℤ)⟧ := (CochainComplex.Plus.ι _).preimageIso
    (((CochainComplex.Plus.ι _).commShiftIso (q : ℤ)).symm.app L)
  let c := DerivedCategory.Plus.Q.mapIso b ≪≫
    (DerivedCategory.Plus.Q.commShiftIso (q : ℤ)).app L
  let t := R.mapCochainComplexPlus.mapIso b ≪≫
    (R.mapCochainComplexPlus.commShiftIso (q : ℤ)).app L
  have hb : b.hom.hom ≫
      ((CochainComplex.Plus.ι _).commShiftIso (q : ℤ)).hom.app L = 𝟙 _ := by
    change (CochainComplex.Plus.ι _).map
      ((CochainComplex.Plus.ι _).preimage _) ≫ _ = _
    erw [Functor.map_preimage, Iso.inv_hom_id_app]
    rfl
  have ht : t.hom.hom ≫
      ((CochainComplex.Plus.ι _).commShiftIso (q : ℤ)).hom.app
        (R.mapCochainComplexPlus.obj L) =
      ((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app
        I.cochainComplex := by
    change (R.mapCochainComplexPlus.map b.hom ≫
        (R.mapCochainComplexPlus.commShiftIso (q : ℤ)).hom.app L).hom ≫ _ = _
    rw [mapped_shift_comparison, hb, CategoryTheory.Functor.map_id, Category.id_comp]
  -- Identify the prescribed augmentation before applying the derived functor.
  have ha : (shiftedAugmentation I q).inv =
      c.hom ≫ a.inv⟦(q : ℤ)⟧' := by
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    apply augmentation_shift_factorization L J (q : ℤ) b
    rw [hb, CategoryTheory.Functor.map_id, Category.id_comp]
    exact resolution_augmentation_ambient q I
  exact resolution_unit_homology_generic R I q J b
    (shiftedAugmentation I q) ha
    (((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app I.cochainComplex)
    ht sigma hsigma tail htail

/-- The unit on the shifted resolution induces the inverse normalized resolution comparison.
Source: Stacks Project, Tag 072W, injective resolution computation of direct images;
Tag 0DVC, the unit of a right derived functor.
(blueprint: lem-weil-pbc-resolution-shifted-unit-homology).

Proof: first work without the shift. The right-derived unit on I is invertible since
I is a bounded below complex of injectives. Naturality along its augmentation identifies
its inverse with the prescribed resolution comparison. Apply homology and the
localization-homology comparison. The comparison from the chosen resolution to I lifts
the identity of F, so naturality of isoRightDerivedObjCochainComplex cancels that comparison
and gives the inverse of the two displayed classical derived-functor isomorphisms.
For the shift, use commShift_rightDerivedFunctorPlusUnit to commute the unit with q,
then naturality with the shifted augmentation. The localization comparison commutes with
shifts, and the homology shift sequence is induced by localization, so its square turns
H^0 of the q-shift into H^q with precisely the displayed shift comparison. These identities
hold also for q=0, the zero sheaf and any choice of injective resolution; no chart or chain
map is part of this assertion. -/
theorem resolution_shifted_unit_homology {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) :
    let R := lowerStar AddCommGrpCat.{u + 1} f
    let J := normalizationShiftedResolution F I q
    let H := DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
    (DerivedCategory.Plus.homologyFunctorObjQIso (R.mapCochainComplexPlus.obj J) 0).inv ≫
        H.map (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient _).obj J)) ≫
        H.map (R.rightDerivedFunctorPlus.map (normalizationShiftedAugmentation F I q).inv) ≫
        (abelianComparisonShift f q F).hom =
      resolutionCocycleHomologyTail f q F I := by
  exact resolution_unit_homology_aux q I (lowerStar AddCommGrpCat.{u + 1} f)
    (abelianComparisonShift f q F) (by rfl) (resolutionCocycleHomologyTail f q F I)
    (by delta resolutionCocycleHomologyTail; rfl)

end AlgebraicGeometry.Etale
