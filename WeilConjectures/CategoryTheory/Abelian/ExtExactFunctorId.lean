/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Ext identity comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: `lem-weil-pbc-ext-exact-functor-identity-comparison`)
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
(blueprint: `lem-weil-pbc-ext-exact-functor-identity-comparison`)
-/
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n) := by
  let := HasDerivedCategory.standard C
  let Q := DerivedCategory.Q (C := C)
  let W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  -- Apply the given comparison termwise, with the identity comparison on complexes.
  let ε : F.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      𝟭 (CochainComplex C ℤ) :=
    e.hom.mapHomologicalComplex _ ≫ (Functor.mapHomologicalComplexIdIso C _).hom
  have : NatTrans.CommShift ε ℤ := by
    constructor
    intro m
    ext K i
    simp [ε, Functor.commShiftIso_id_hom_app]
  let δ : Q ⋙ F.mapDerivedCategory ⟶ Q ⋙ 𝟭 (DerivedCategory C) :=
    F.mapDerivedCategoryFactors.hom ≫ Functor.whiskerRight ε Q ≫
      Q.leftUnitor.hom ≫ Q.rightUnitor.inv
  have : NatTrans.CommShift Q.rightUnitor.inv ℤ :=
    NatTrans.CommShift.of_iso_inv Q.rightUnitor ℤ
  have : NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ := inferInstance
  have : NatTrans.CommShift (Functor.whiskerRight ε Q) ℤ := inferInstance
  have : NatTrans.CommShift δ ℤ := by dsimp [δ]; infer_instance
  -- Fullness of precomposition lifts the comparison to the derived category.
  have := Localization.full_whiskeringLeft Q W (DerivedCategory C)
  let τ : F.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C) :=
    (Functor.whiskeringLeft _ _ _).obj Q |>.preimage δ
  have hτ : Functor.whiskerLeft Q τ = δ :=
    Functor.map_preimage ((Functor.whiskeringLeft _ _ _).obj Q) δ
  have : NatTrans.CommShift (Functor.whiskerLeft Q τ) ℤ := by
    rw [hτ]
    infer_instance
  have : NatTrans.CommShift τ ℤ := commShift_of_localization (W := W) Q τ
  -- Identify its components after the canonical single-complex comparisons.
  have hsingle (Z : C) :
      (F.mapDerivedCategorySingleFunctor 0).inv.app Z ≫
        τ.app ((DerivedCategory.singleFunctor C 0).obj Z) =
      (DerivedCategory.singleFunctor C 0).map (e.hom.app Z) := by
    have h := congr_app hτ ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z)
    dsimp [δ, Q] at h
    rw [h]
    simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id,
      Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc,
      ε, NatTrans.comp_app, ← Functor.map_comp]
    change DerivedCategory.Q.map _ =
      DerivedCategory.Q.map ((HomologicalComplex.single C (.up ℤ) 0).map (e.hom.app Z))
    congr 1
    ext
    simp [HomologicalComplex.single,
      Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, HomologicalComplex.singleMapHomologicalComplex]
  -- Naturality for the shifted morphism is the required Ext identity.
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  have h := ShiftedHom.map_naturality x.hom τ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.id_map] at h
  rw [← hsingle X, ← hsingle Y]
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  simpa [Category.assoc] using
    congrArg ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ ·) h

end CategoryTheory.Abelian.Ext
