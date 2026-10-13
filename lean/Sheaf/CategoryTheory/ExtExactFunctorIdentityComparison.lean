/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

/-!
# Ext identity comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

/-- Shift compatibility descends along localization: check the square after precomposition,
then cancel the image of the localization functor's shift comparison. -/
private theorem commShift_of_localization
    {A B : Type*} [Category A] [Category B]
    {W : MorphismProperty A} (L : A ⥤ B) [L.IsLocalization W]
    [HasShift A ℤ] [HasShift B ℤ] [L.CommShift ℤ]
    {F G : B ⥤ B} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  apply Localization.natTrans_ext L W
  intro K
  dsimp
  rw [← cancel_epi (F.map ((L.commShiftIso n).hom.app K))]
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) n K
  simpa only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc, ← τ.naturality_assoc] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An exact functor isomorphic to the identity acts on Ext by that comparison.
Source: Stacks Project, derived.tex, Tag 015F, and Mathlib Ext.Map.

Proof: represent x by a shifted morphism between single complexes in the derived
category. The identity functor on complexes induces the identity after localization.
The components of e induce the corresponding isomorphism from the functor induced by F
to the identity. Naturality for the shifted morphism is exactly the displayed square.
After cancelling the canonical comparisons with single complexes and shifts, its
components are Ext.mk₀ (e.hom.app X) and Ext.mk₀ (e.hom.app Y).
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n) := by
  let := HasDerivedCategory.standard C
  have hid {A B : C} (z : Ext.{w} A B n) : z.mapExactFunctor (𝟭 C) = z := by
    let Q := DerivedCategory.Q (C := C)
    let ε := Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)
    have : NatTrans.CommShift ε.hom ℤ := by
      constructor
      intro m
      ext K i
      simp [ε, Functor.commShiftIso_id_hom_app]
    let δ := Functor.isoWhiskerRight ε Q ≪≫ Q.leftUnitor ≪≫ Q.rightUnitor.symm
    have : NatTrans.CommShift Q.rightUnitor.inv ℤ :=
      NatTrans.CommShift.of_iso_inv Q.rightUnitor ℤ
    have : NatTrans.CommShift δ.hom ℤ := by dsimp [δ]; infer_instance
    have h := ((𝟭 C).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).equiv_smallShiftedHomMap Q Q
        (((𝟭 C).mapCochainComplexSingleFunctor 0).app A)
        (((𝟭 C).mapCochainComplexSingleFunctor 0).app B) (𝟭 _) δ z
    have hx (Z : C) :
        Q.map (((𝟭 C).mapCochainComplexSingleFunctor 0).app Z).inv ≫
          δ.hom.app ((CochainComplex.singleFunctor C 0).obj Z) =
        𝟙 (Q.obj ((CochainComplex.singleFunctor C 0).obj Z)) := by
      dsimp [δ]
      simp only [Category.comp_id, ← Q.map_comp]
      rw [← Q.map_id]
      congr 1
      ext i
      dsimp [Functor.mapCochainComplexSingleFunctor,
        HomologicalComplex.singleMapHomologicalComplex, ε,
        Functor.mapHomologicalComplexIdIso, CochainComplex.singleFunctor,
        CochainComplex.singleFunctors, HomologicalComplex.single]
      by_cases hi : i = 0
      · subst i; simp
      · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Z i hi
        exact hz.eq_of_src _ _
    have hy (Z : C) :
        δ.inv.app ((CochainComplex.singleFunctor C 0).obj Z) ≫
          Q.map (((𝟭 C).mapCochainComplexSingleFunctor 0).app Z).hom =
        𝟙 (Q.obj ((CochainComplex.singleFunctor C 0).obj Z)) := by
      rw [← cancel_epi (δ.hom.app ((CochainComplex.singleFunctor C 0).obj Z))]
      simp only [Iso.hom_inv_id_app_assoc]
      rw [← cancel_epi (Q.map (((𝟭 C).mapCochainComplexSingleFunctor 0).app Z).inv)]
      erw [Category.comp_id, hx]
      dsimp only [Iso.app_inv, Iso.app_hom]
      rw [← Q.map_comp, Iso.inv_hom_id_app, Q.map_id]
      rfl
    apply Ext.ext
    change _ = z.hom
    change (z.mapExactFunctor (𝟭 C)).hom = _ at h
    rw [h, hx, hy]
    simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.id_map]
    change 𝟙 _ ≫ z.hom ≫ (shiftFunctor _ _).map (𝟙 _) = z.hom
    simp
  -- Specialize the composition comparison to the identity functor.
  have h := mapExactFunctor_comp_mk₀_eq (𝟭 C) (𝟭 C) F
    (e ≪≫ (𝟭 C).rightUnitor.symm) x
  simpa [hid] using h


end CategoryTheory.Abelian.Ext
