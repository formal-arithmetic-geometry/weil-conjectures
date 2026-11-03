/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback
public import WeilConjectures.CategoryTheory.OrientationGlobalClassTransport
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.OrientationGlobalClassBounded
import WeilConjectures.CategoryTheory.OrientationGlobalClassDegreeOne
import all Mathlib.Algebra.Homology.DerivedCategory.Plus
import all Mathlib.CategoryTheory.Shift.SingleFunctorsLift
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Evaluation of Ext pullback squares

Source: Milne, Theorem 9.4, and Stacks Tag 05TD.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' d e f
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian.Ext

attribute [local implicit_reducible] DerivedCategory.Plus.singleFunctors
  DerivedCategory.singleFunctors SingleFunctors.lift SingleFunctors.postcomp
  DerivedCategory.Plus.homologyFunctor Functor.shift Functor.mapDerivedCategoryPlus

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]
  [HasDerivedCategory.{u'} C] [EnoughInjectives C] [HasKInjectiveResolutions C]
  {C' : Type v'} [Category.{w'} C'] [Abelian C'] [HasExt.{d} C']
  [HasDerivedCategory.{e} C'] [EnoughInjectives C'] [HasKInjectiveResolutions C']
  {D : Type f} [Category D] [Abelian D] [HasDerivedCategory D]

private def boundedClassHom {A B : C} (x : Ext.{u} A B 1) :
    (DerivedCategory.Plus.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj B)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (x.hom ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj B))

omit [EnoughInjectives C] [HasKInjectiveResolutions C] in
private theorem boundedClassHom_spec {A B : C} (x : Ext.{u} A B 1) :
    DerivedCategory.Plus.ι.map (boundedClassHom x) ≫
      (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _ = x.hom := by
  dsimp only [boundedClassHom]
  erw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

omit [EnoughInjectives C] [HasKInjectiveResolutions C]
  [EnoughInjectives C'] [HasKInjectiveResolutions C'] in
private theorem boundedClassHom_pullback
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A B : C} {A' B' : C'} (a : L.obj A ⟶ A') (b : L.obj B ⟶ B')
    (x : Ext.{u} A B 1) (y : Ext.{d} A' B' 1)
    (h : (x.mapExactFunctor L).comp (mk₀ b) (add_zero 1) =
      (mk₀ a).comp y (zero_add 1)) :
    L.mapDerivedCategoryPlus.map (boundedClassHom x) ≫
        (L.mapDerivedCategoryPlus.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app B ≫
          (DerivedCategory.Plus.singleFunctor C' 0).map b)⟦(1 : ℤ)⟧' =
      ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
        (DerivedCategory.Plus.singleFunctor C' 0).map a) ≫ boundedClassHom y := by
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _)).1
  have hh := congrArg (fun z ↦ z.hom) h
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    Ext.mapExactFunctor_hom, ShiftedHom.map] at hh
  simp only [Functor.map_comp, Category.assoc]
  erw [DerivedCategory.Plus.ι.commShiftIso_hom_naturality]
  erw [DerivedCategory.Plus.ι.commShiftIso_hom_naturality_assoc,
    reassoc_of% (L.ι_map_mapDerivedCategoryPlus_commShiftIso_hom_app (1 : ℤ)
      ((DerivedCategory.Plus.singleFunctor C 0).obj B))]
  erw [← L.mapDerivedCategory.map_comp_assoc, boundedClassHom_spec,
    L.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    L.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  erw [← Category.assoc, boundedClassHom_spec]
  erw [← cancel_epi ((L.mapDerivedCategorySingleFunctor 0).inv.app A)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc] at hh ⊢
  convert hh using 1 <;> rfl

/-- A coefficient square of degree-one Ext classes gives the corresponding square
on their derived evaluations.
Source: Milne Theorem 9.4, and Stacks Tag 05TD.
Proof: lift the two derived morphisms through the fully faithful bounded-below
inclusion. Exact inverse image carries their Ext square to the bounded-below square.
The normalized transport respects shifts and its degree-zero augmentation. Apply
naturality of degree-one evaluation and the bounded/unbounded evaluation comparison.
(blueprint: lem-pur-orientation-global-class-evaluation). -/
theorem orientationGlobalClassMap_exact_naturality
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (E : C ⥤ D) (E' : C' ⥤ D) [E.Additive] [E'.Additive] (τ : E ⟶ L ⋙ E')
    {A B : C} {A' B' : C'} (a : L.obj A ⟶ A') (b : L.obj B ⟶ B')
    (x : Ext.{u} A B 1) (y : Ext.{d} A' B' 1)
    (h : (x.mapExactFunctor L).comp (mk₀ b) (add_zero 1) =
      (mk₀ a).comp y (zero_add 1)) :
    coordinateSectionMap E x ≫
        (DerivedCategory.Plus.homologyFunctor D 1).map
          ((Functor.orientationGlobalClassTransport L E E' τ).app
              ((DerivedCategory.Plus.singleFunctor C 0).obj B) ≫
            E'.rightDerivedFunctorPlus.map
              ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app B ≫
                (DerivedCategory.Plus.singleFunctor C' 0).map b)) =
      τ.app A ≫ E'.map a ≫ coordinateSectionMap E' y := by
  let η := Functor.orientationGlobalClassTransport L E E' τ
  have : NatTrans.CommShift η ℤ := Functor.orientationGlobalClassTransport_shift L E E' τ
  let uA := E.toRightDerivedZero.app A ≫
    (E.homologyRightDerivedFunctorPlusObjSingleFunctorIso A 0).inv
  let uA' := τ.app A ≫ E'.map a ≫ E'.toRightDerivedZero.app A' ≫
    (E'.homologyRightDerivedFunctorPlusObjSingleFunctorIso A' 0).inv
  have hu : uA ≫ (DerivedCategory.Plus.homologyFunctor D 0).map
      (η.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) ≫
        E'.rightDerivedFunctorPlus.map
          ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
            (DerivedCategory.Plus.singleFunctor C' 0).map a)) = uA' := by
    dsimp only [uA, uA', η]
    simp only [Functor.map_comp, Category.assoc]
    erw [← Functor.map_comp_assoc,
      reassoc_of% (Functor.orientationGlobalClassTransport_zero_unit L E E' τ A)]
    have hn :=
      (E'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.naturality a
    have ht := E'.toRightDerivedZero.naturality a
    dsimp only [Functor.comp_map] at hn ht
    change τ.app A ≫ E'.toRightDerivedZero.app (L.obj A) ≫
        (E'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.app
          (L.obj A) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (E'.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C' 0).map a)) =
      τ.app A ≫ E'.map a ≫ E'.toRightDerivedZero.app A' ≫
        (E'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.app A'
    erw [← hn, ← reassoc_of% ht]
  have he := orientationGlobalClass_degree_one_evaluation_naturality L.mapDerivedCategoryPlus
    E.rightDerivedFunctorPlus E'.rightDerivedFunctorPlus η
    ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map a)
    ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app B ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map b)
    (boundedClassHom x) (boundedClassHom y)
    (boundedClassHom_pullback L a b x y h) uA uA' hu
  erw [orientationGlobalClassMap_bounded E x _ (boundedClassHom_spec x),
    orientationGlobalClassMap_bounded E' y _ (boundedClassHom_spec y)]
  simpa only [uA, uA', Category.assoc] using he

end CategoryTheory.Abelian.Ext
