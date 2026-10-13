/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.ModuleObjects.Basic

/-!

# The category of module objects is preadditive

If `C` is a preadditive monoidal category whose tensor product is additive in each variable
(`MonoidalPreadditive C`), then for every algebra object `R : C` the category `Mod C R` of left
`R`-module objects is preadditive: sums and negatives of `R`-linear morphisms are computed in `C`.
The forgetful functor `Mod C R ⥤ C` is additive.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Preadditive

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

@[simp]
lemma whiskerLeft_neg (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ (-f) = -(X ◁ f) :=
  (tensorLeft X).map_neg

@[simp]
lemma neg_whiskerRight {Y Z : C} (f : Y ⟶ Z) (X : C) : (-f) ▷ X = -(f ▷ X) :=
  (tensorRight X).map_neg

@[simp]
lemma whiskerLeft_sub (X : C) {Y Z : C} (f g : Y ⟶ Z) : X ◁ (f - g) = X ◁ f - X ◁ g :=
  (tensorLeft X).map_sub

@[simp]
lemma sub_whiskerRight {Y Z : C} (f g : Y ⟶ Z) (X : C) : (f - g) ▷ X = f ▷ X - g ▷ X :=
  (tensorRight X).map_sub

@[simp]
lemma whiskerLeft_nsmul (X : C) {Y Z : C} (n : ℕ) (f : Y ⟶ Z) : X ◁ (n • f) = n • (X ◁ f) :=
  (tensorLeft X).map_nsmul

@[simp]
lemma nsmul_whiskerRight {Y Z : C} (n : ℕ) (f : Y ⟶ Z) (X : C) : (n • f) ▷ X = n • (f ▷ X) :=
  (tensorRight X).map_nsmul

@[simp]
lemma whiskerLeft_zsmul (X : C) {Y Z : C} (n : ℤ) (f : Y ⟶ Z) : X ◁ (n • f) = n • (X ◁ f) :=
  (tensorLeft X).map_zsmul

@[simp]
lemma zsmul_whiskerRight {Y Z : C} (n : ℤ) (f : Y ⟶ Z) (X : C) : (n • f) ▷ X = n • (f ▷ X) :=
  (tensorRight X).map_zsmul

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] {R : C} [MonObj R]

section

variable {M N : Mod C R}

instance moduleObjectInstance_Preadditive_1 : Zero (M ⟶ N) := ⟨Hom.mk' 0 (by simp)⟩

instance moduleObjectInstance_Preadditive_2 : Add (M ⟶ N) :=
  ⟨fun f g ↦ Hom.mk' (f.hom + g.hom) (by
    change γ[R,M.X] ≫ (f.hom + g.hom) = R ◁ (f.hom + g.hom) ≫ γ[R,N.X]
    simp [comp_add, add_comp])⟩

instance moduleObjectInstance_Preadditive_3 : Neg (M ⟶ N) :=
  ⟨fun f ↦ Hom.mk' (-f.hom) (by
    change γ[R,M.X] ≫ (-f.hom) = R ◁ (-f.hom) ≫ γ[R,N.X]
    simp [comp_neg])⟩

instance moduleObjectInstance_Preadditive_4 : Sub (M ⟶ N) :=
  ⟨fun f g ↦ Hom.mk' (f.hom - g.hom) (by
    change γ[R,M.X] ≫ (f.hom - g.hom) = R ◁ (f.hom - g.hom) ≫ γ[R,N.X]
    simp [comp_sub])⟩

instance moduleObjectInstance_Preadditive_5 : SMul ℕ (M ⟶ N) :=
  ⟨fun n f ↦ Hom.mk' (n • f.hom) (by
    change γ[R,M.X] ≫ (n • f.hom) = R ◁ (n • f.hom) ≫ γ[R,N.X]
    simp [comp_nsmul, nsmul_comp])⟩

instance moduleObjectInstance_Preadditive_6 : SMul ℤ (M ⟶ N) :=
  ⟨fun n f ↦ Hom.mk' (n • f.hom) (by
    change γ[R,M.X] ≫ (n • f.hom) = R ◁ (n • f.hom) ≫ γ[R,N.X]
    simp [comp_zsmul, zsmul_comp])⟩

@[simp] lemma moduleObject_zero_hom : (0 : M ⟶ N).hom = 0 := rfl

@[simp] lemma moduleObject_add_hom (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

@[simp] lemma moduleObject_neg_hom (f : M ⟶ N) : (-f).hom = -f.hom := rfl

@[simp] lemma sub_hom (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

@[simp] lemma nsmul_hom (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

@[simp] lemma zsmul_hom (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance moduleObjectInstance_Preadditive_7 : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f ↦ f.hom) (fun _ _ h ↦ hom_ext _ _ h) rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end

instance moduleObjectInstance_Preadditive_8 : Preadditive (Mod C R) where
  add_comp _ _ _ _ _ _ := hom_ext _ _ (add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := hom_ext _ _ (comp_add _ _ _ _ _ _)

instance moduleObjectInstance_Preadditive_9 : (forget R : Mod C R ⥤ C).Additive where

end CategoryTheory.Mod
