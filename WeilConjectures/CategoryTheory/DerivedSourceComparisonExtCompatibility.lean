/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Compatibility of Ext resolution maps with displayed bounded-below derived morphisms. -/

@[expose] public section

universe v u₁ u₂
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory

@[no_expose] noncomputable def sourceExtMap
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L) (Y : C) (q : ℕ) :
    Abelian.Ext L Y q →+ Abelian.Ext B (V.obj Y) q :=
  ((Abelian.Ext.mk₀ a).precomp _ (zero_add q)).comp (V.mapExtAddHom L Y q)


set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the Ext resolution map with the displayed derived morphism: if two
morphisms `x y` from `L[0]` to `Y[0][q]` in the bounded below derived category agree after
precomposition with the image of `a`, then their images under `sourceExtMap` agree. -/
theorem derivedSourceComparison_ext_compatibility
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L) (Y : C) (q : ℕ)
    (x y : (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦(q : ℤ)⟧)
    (hxy : ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map x =
      ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map y) :
    sourceExtMap V L B a Y q
      (Abelian.Ext.homEquiv.symm (ShiftedHom.map x (DerivedCategory.Plus.ι (C := C)))) =
    sourceExtMap V L B a Y q
      (Abelian.Ext.homEquiv.symm (ShiftedHom.map y (DerivedCategory.Plus.ι (C := C)))) := by
  apply Abelian.Ext.homEquiv.injective
  change ((Abelian.Ext.mk₀ a).comp
    ((Abelian.Ext.homEquiv.symm (ShiftedHom.map x
      (DerivedCategory.Plus.ι (C := C)))).mapExactFunctor V) (zero_add q)).hom =
    ((Abelian.Ext.mk₀ a).comp
    ((Abelian.Ext.homEquiv.symm (ShiftedHom.map y
      (DerivedCategory.Plus.ι (C := C)))).mapExactFunctor V) (zero_add q)).hom
  simp only [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.map, Equiv.apply_symm_apply, Category.assoc]
  have hinv : DerivedCategory.Plus.ι.map
      ((V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) =
      (V.mapDerivedCategorySingleFunctor 0).inv.app L := by
    apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app L)).1
    rw [← V.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rw [V.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app, Iso.inv_hom_id_app]
    rfl
  have hh := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z) hxy
  simp only [Functor.map_comp, hinv, Category.assoc] at hh
  change (DerivedCategory.singleFunctor D 0).map a ≫
    (V.mapDerivedCategorySingleFunctor 0).inv.app L ≫
      V.mapDerivedCategory.map (DerivedCategory.Plus.ι.map x) =
    (DerivedCategory.singleFunctor D 0).map a ≫
    (V.mapDerivedCategorySingleFunctor 0).inv.app L ≫
      V.mapDerivedCategory.map (DerivedCategory.Plus.ι.map y) at hh
  have hh' := congrArg (fun z ↦ z ≫
    V.mapDerivedCategory.map ((DerivedCategory.Plus.ι.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y)) ≫
    (V.mapDerivedCategory.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.singleFunctor C 0).obj Y) ≫
    ((V.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(q : ℤ)⟧') hh
  simpa only [Functor.map_comp, Category.assoc] using hh'

end CategoryTheory
