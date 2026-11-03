/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import all WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalRealizationShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.Plus
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Shift.SingleFunctorsLift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Shift.InducedShiftSequence

/-! # Naturality of evaluation of coordinate Ext classes
Source: Milne, Theorem 9.4, and Stacks Tag 05TD. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u u' v v' w w' d
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

attribute [local implicit_reducible] DerivedCategory.Plus.homologyFunctor
  DerivedCategory.Plus.singleFunctors DerivedCategory.singleFunctors
  SingleFunctors.lift SingleFunctors.postcomp Functor.shift Functor.ShiftSequence.induced

/-- The bounded and unbounded realizations evaluate the same degree-one Ext class.
Source: Milne Theorem 9.4; Stacks Tag 05TD.
Proof: naturality of the comparison between the two derived functors moves it across
the bounded representative of the class. Its shift compatibility moves it through
the degree-one shift. The homology-shift comparison is natural, and the two inverse
comparison factors cancel. The remaining degree-zero comparison is the prescribed
single-object identification.
(blueprint: aux-lem-pur-coordinate-class-section-naturality). -/
theorem coordinateSectionMap_bounded
    {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
    [HasDerivedCategory.{u'} C] [EnoughInjectives C] [HasKInjectiveResolutions C]
    {D : Type v'} [Category.{w'} D] [Abelian D] [HasDerivedCategory.{d} D]
    (E : C ⥤ D) [E.Additive] {B F : C} (c : Ext.{u} B F 1)
    (x : (DerivedCategory.Plus.singleFunctor C 0).obj B ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj F)⟦(1 : ℤ)⟧)
    (hx : DerivedCategory.Plus.ι.map x ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj F) = c.hom) :
    coordinateSectionMap E c =
      E.toRightDerivedZero.app B ≫
        (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso B 0).inv ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (E.rightDerivedFunctorPlus.map x ≫
            (E.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app _) ≫
        ((DerivedCategory.Plus.homologyFunctor D 0).shiftIso (1 : ℤ) 0 1
          (add_zero 1)).hom.app _ := by
  have := AlgebraicGeometry.ProEtale.rightDerivedCompatibility_shift E
  let e := E.rightDerivedFunctorPlusCompatibility
  have hn := e.hom.naturality x
  have hs := NatTrans.shift_app_comm e.hom (1 : ℤ)
    ((DerivedCategory.Plus.singleFunctor C 0).obj F)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.commShiftIso_comp_hom_app] at hs
  have hc : e.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj B) ≫
      E.rightDerivedFunctor.map c.hom ≫
        (E.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app _ =
    DerivedCategory.Plus.ι.map (E.rightDerivedFunctorPlus.map x ≫
      (E.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app _) ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          (E.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj F)) ≫
        (e.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj F))⟦(1 : ℤ)⟧' := by
    erw [← hx, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    erw [← reassoc_of% hn]
    have hz := congrArg (fun z ↦
      DerivedCategory.Plus.ι.map (E.rightDerivedFunctorPlus.map x) ≫ z) hs.symm
    simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hz ⊢
    convert hz using 1 <;> rfl
  unfold coordinateSectionMap
  simp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso, Iso.trans_inv,
    Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.whiskerRight_app, Functor.mapIso_inv, Iso.symm_inv,
    Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, hc,
    CategoryTheory.Functor.map_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hh := (DerivedCategory.homologyFunctor D 0).shiftIso_hom_naturality
    (1 : ℤ) 0 1 (add_zero 1)
      (e.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj F))
  have hh' := congrArg (fun z ↦ z ≫ (DerivedCategory.homologyFunctor D 1).map
    (e.inv.app ((DerivedCategory.Plus.singleFunctor C 0).obj F))) hh
  simp only [DerivedCategory.shift_homologyFunctor, Category.assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id, Category.comp_id] at hh'
  erw [hh']
  simp only [Functor.shiftIso, Functor.ShiftSequence.leftComp_shiftIso,
    Iso.trans_hom, Iso.symm_hom, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, Category.id_comp]
  simp only [DerivedCategory.shift_homologyFunctor,
    DerivedCategory.Plus.homologyFunctor, Functor.comp_map]
  erw [Category.id_comp]
  rfl

end CategoryTheory.Abelian.Ext
