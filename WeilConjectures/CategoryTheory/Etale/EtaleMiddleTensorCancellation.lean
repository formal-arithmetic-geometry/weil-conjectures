/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Removing a normalized tensor factor from a tensor cocycle -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory

namespace CategoryTheory

@[reassoc]
private theorem middle_fold
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      F.map (f ▷ B) ≫ (δ A' B).hom = (δ A B).hom ≫ F.map f ▷ F.obj B)
    (hu : ∀ B : C, (δ (𝟙_ C) B).hom ≫ ε.hom ▷ F.obj B ≫
      (λ_ (F.obj B)).hom = F.map (λ_ B).hom)
    (W : D) (M N : C) (η : M ≅ 𝟙_ C) :
    (α_ W (F.obj M) (F.obj N)).hom ≫ W ◁ (δ M N).inv ≫
        W ◁ F.map (η.hom ▷ N ≫ (λ_ N).hom) =
      ((W ◁ (F.map η.hom ≫ ε.hom) ≫ (ρ_ W).hom) ⊗ₘ 𝟙 (F.obj N)) := by
  have h : F.map (η.hom ▷ N ≫ (λ_ N).hom) =
      (δ M N).hom ≫ (F.map η.hom ≫ ε.hom) ▷ F.obj N ≫
        (λ_ (F.obj N)).hom := by
    rw [F.map_comp, ← hu, ← Category.assoc, hn]
    simp only [comp_whiskerRight, Category.assoc]
  rw [h]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_inv_hom_assoc]
  rw [← associator_naturality_middle_assoc, triangle]
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]

/-- A tensor cocycle whose middle factor is normalized by a map to the unit can be
cancelled. Source: the tensor-unit calculation in the composition-coherence proof,
Step 1 (blueprint: lem-pur-etale-middle-tensor-cancellation).

Proof: naturality of the tensor constraint at eta and its left-unit law identify
the image of the normalized multiplication with the left unitor after the tensor
constraint. The associator triangle turns this into the right-unit map on W,
tensored with the identity. Precompose the desired equation with the invertible
associator, inverse tensor constraint and image of tau. The cocycle rewrites its
left side; the normalization of tau and this unit calculation rewrite its right
side to the same map. This works in arbitrary monoidal categories, including
zero objects and identity normalization maps. -/
private theorem normalized_middle_tensor_cancellation
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      F.map (f ▷ B) ≫ (δ A' B).hom = (δ A B).hom ≫ F.map f ▷ F.obj B)
    (hu : ∀ B : C, (δ (𝟙_ C) B).hom ≫ ε.hom ▷ F.obj B ≫
      (λ_ (F.obj B)).hom = F.map (λ_ B).hom)
    (W A T : D) (M N B : C) (η : M ≅ 𝟙_ C)
    (τ : M ⊗ N ≅ B) (e : B ≅ N)
    (s : W ⊗ F.obj M ⟶ A) (t : A ⊗ F.obj N ⟶ T)
    (v : W ⊗ F.obj B ⟶ T)
    (hτ : τ.hom ≫ e.hom = η.hom ▷ N ≫ (λ_ N).hom)
    (hc : (s ⊗ₘ 𝟙 (F.obj N)) ≫ t =
      (α_ W (F.obj M) (F.obj N)).hom ≫ W ◁ (δ M N).inv ≫
        W ◁ F.map τ.hom ≫ v) :
    let U : W ⊗ F.obj M ≅ W :=
      (whiskerLeftIso W (F.mapIso η ≪≫ ε)) ≪≫ ρ_ W
    v = (W ◁ F.map e.hom) ≫ ((U.inv ≫ s) ⊗ₘ 𝟙 (F.obj N)) ≫ t := by
  intro U
  apply (cancel_epi ((α_ W (F.obj M) (F.obj N)).hom ≫
    W ◁ (δ M N).inv ≫ W ◁ F.map τ.hom)).1
  simp only [Category.assoc]
  rw [← hc]
  rw [← whiskerLeft_comp_assoc W (F.map τ.hom) (F.map e.hom),
    ← F.map_comp, hτ]
  rw [middle_fold_assoc F δ ε hn hu W M N η]
  change (s ⊗ₘ 𝟙 (F.obj N)) ≫ t =
    (U.hom ⊗ₘ 𝟙 (F.obj N)) ≫ ((U.inv ≫ s) ⊗ₘ 𝟙 (F.obj N)) ≫ t
  simp only [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_assoc,
    Category.comp_id]

/-- The same normalized cancellation with an explicit third-factor compositor.
Source: the etale middle-arrow calculation in composition coherence Step 1
(blueprint: lem-pur-etale-middle-tensor-cancellation).

Proof: the normalization makes the middle multiplication the isomorphism
eta tensor identity, followed by the unitor and inverse e. Precompose the
cocycle with the inverse third-factor compositor. Tensor interchange and
associator naturality cancel that compositor on the right. Apply normalized
middle cancellation, then combine the two tensor maps on the left. -/
theorem normalized_middle_cocycle_cancellation
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      F.map (f ▷ B) ≫ (δ A' B).hom = (δ A B).hom ≫ F.map f ▷ F.obj B)
    (hu : ∀ B : C, (δ (𝟙_ C) B).hom ≫ ε.hom ▷ F.obj B ≫
      (λ_ (F.obj B)).hom = F.map (λ_ B).hom)
    (W A T X : D) (M N B : C) (η : M ≅ 𝟙_ C)
    (e : B ≅ N) (c : X ≅ F.obj N)
    (s : W ⊗ F.obj M ⟶ A) (t : A ⊗ X ⟶ T)
    (v : W ⊗ F.obj B ⟶ T) (k : M ⊗ N ⟶ B)
    (hk : k ≫ e.hom = η.hom ▷ N ≫ (λ_ N).hom)
    (hc : (s ⊗ₘ 𝟙 X) ≫ t =
      (α_ W (F.obj M) X).hom ≫
        W ◁ ((F.obj M ◁ c.hom) ≫ (δ M N).inv ≫ F.map k) ≫ v) :
    let U : W ⊗ F.obj M ≅ W :=
      whiskerLeftIso W (F.mapIso η ≪≫ ε) ≪≫ ρ_ W
    v = (W ◁ F.map e.hom) ≫ ((U.inv ≫ s) ⊗ₘ c.inv) ≫ t := by
  intro U
  let τ : M ⊗ N ≅ B := (whiskerRightIso η N ≪≫ λ_ N) ≪≫ e.symm
  have hτ : k = τ.hom := by
    apply (cancel_mono e.hom).1
    simpa only [τ, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, whiskerRightIso_hom] using hk
  let t' := (𝟙 A ⊗ₘ c.inv) ≫ t
  have hc' : (s ⊗ₘ 𝟙 (F.obj N)) ≫ t' =
      (α_ W (F.obj M) (F.obj N)).hom ≫ W ◁ (δ M N).inv ≫
        W ◁ F.map τ.hom ≫ v := by
    rw [hτ] at hc
    have hh := congrArg (fun z ↦ ((W ⊗ F.obj M) ◁ c.inv) ≫ z) hc
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id,
      whiskerLeft_comp, Category.assoc] at hh
    rw [whisker_exchange_assoc, associator_naturality_right_assoc] at hh
    rw [← whiskerLeft_comp_assoc, whiskerLeft_inv_hom,
      whiskerLeft_id, Category.id_comp] at hh
    simpa only [t', tensorHom_def, whiskerLeft_id, id_whiskerRight,
      Category.comp_id, Category.id_comp, Category.assoc] using hh
  have hτ' : τ.hom ≫ e.hom = η.hom ▷ N ≫ (λ_ N).hom := by
    rw [← hτ]
    exact hk
  have hh := normalized_middle_tensor_cancellation F δ ε hn hu
    W A T M N B η τ e s t' v hτ' hc'
  simpa only [t', tensorHom_comp_tensorHom_assoc, Category.assoc,
    Category.comp_id, Category.id_comp] using hh

end CategoryTheory
