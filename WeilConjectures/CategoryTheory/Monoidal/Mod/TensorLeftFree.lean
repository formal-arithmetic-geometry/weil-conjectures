/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
# Tensoring with a free module of finite rank preserves monomorphisms

For a module `M` over a commutative monoid `A` in an abelian monoidal category which is free of
finite rank, `M ≅ Aⁿ`, the functor `- ⊗_A M` preserves monomorphisms
(`CategoryTheory.Mod.mono_tensorLeft_map_of_iso_biproduct`): `- ⊗_A ⨁ᵢ Mᵢ` is the direct sum of
the `- ⊗_A Mᵢ`, and `- ⊗_A A ≅ 𝟭`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {A : C}
  [MonObj A] [IsCommMonObj A]
  [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- `- ⊗_A ·` as an additive map on morphisms. -/
@[simps]
noncomputable def tensorLeftMapAddHom (M M' : Mod C A) :
    (M ⟶ M') →+ (tensorLeft M ⟶ tensorLeft M') where
  toFun := tensorLeftMap
  map_zero' := by
    have h := tensorLeftMap_add (0 : M ⟶ M') 0
    rwa [add_zero, left_eq_add] at h
  map_add' := tensorLeftMap_add

lemma sum_tensorLeftMap_π_comp_tensorLeftMap_ι {n : ℕ} (M : Fin n → Mod C A) :
    ∑ i, tensorLeftMap (biproduct.π M i) ≫ tensorLeftMap (biproduct.ι M i) =
      𝟙 (tensorLeft (⨁ M)) := by
  simp_rw [← tensorLeftMap_comp]
  calc ∑ i, tensorLeftMap (biproduct.π M i ≫ biproduct.ι M i) =
      tensorLeftMapAddHom (⨁ M) (⨁ M) (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
        rw [map_sum]; rfl
    _ = 𝟙 _ := by rw [biproduct.total]; exact tensorLeftMap_id _

/-- `- ⊗_A ⨁ᵢ Mᵢ` preserves monomorphisms if each `- ⊗_A Mᵢ` does. -/
lemma mono_tensorLeft_biproduct_map {n : ℕ} (M : Fin n → Mod C A) {N N' : Mod C A}
    (f : N ⟶ N') (h : ∀ i, Mono ((tensorLeft (M i)).map f)) :
    Mono ((tensorLeft (⨁ M)).map f) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
  have htot := sum_tensorLeftMap_π_comp_tensorLeftMap_ι M
  have hi (i : Fin n) : g ≫ (tensorLeftMap (biproduct.π M i)).app N = 0 := by
    have := h i
    rw [← cancel_mono ((tensorLeft (M i)).map f), Category.assoc,
      ← (tensorLeftMap (biproduct.π M i)).naturality, ← Category.assoc, hg, zero_comp,
      zero_comp]
  rw [← Category.comp_id g, ← NatTrans.id_app, ← htot, NatTrans.app_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [NatTrans.comp_app, ← Category.assoc, hi, zero_comp]

/-- `- ⊗_A M` preserves monomorphisms for `M` free of finite rank. -/
lemma mono_tensorLeft_map_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) {N N' : Mod C A} (f : N ⟶ N') [Mono f] :
    Mono ((tensorLeft M).map f) := by
  have : Mono ((tensorLeft (⨁ fun _ : Fin n ↦ regular A)).map f) :=
    mono_tensorLeft_biproduct_map _ f fun _ ↦ by
      rw [← NatIso.naturality_2 tensorLeftRegularIso f]
      infer_instance
  have e' : tensorLeft M ≅ tensorLeft (⨁ fun _ : Fin n ↦ regular A) :=
    { hom := tensorLeftMap e.hom
      inv := tensorLeftMap e.inv
      hom_inv_id := by rw [← tensorLeftMap_comp, e.hom_inv_id, tensorLeftMap_id]
      inv_hom_id := by rw [← tensorLeftMap_comp, e.inv_hom_id, tensorLeftMap_id] }
  rw [← NatIso.naturality_2 e' f]
  infer_instance

end CategoryTheory.Mod
