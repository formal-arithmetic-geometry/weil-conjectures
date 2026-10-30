/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Isomorphisms multiplied by a sign, and averages over colimits

In a preadditive category, an isomorphism `e : X ≅ Y` multiplied by a sign `ε : ℤˣ` is again an
isomorphism (`CategoryTheory.Iso.unitsSMul`).

An endomorphism of a colimit which is levelwise an average of endomorphisms fixes every map out
of the colimit invariant under them
(`CategoryTheory.Limits.IsColimit.comp_eq_of_sum_const_comp_eq_sum`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C]

/-- An isomorphism multiplied by a sign `ε : ℤˣ`. -/
@[simps]
def Iso.unitsSMul {X Y : C} (ε : ℤˣ) (e : X ≅ Y) : X ≅ Y where
  hom := ε • e.hom
  inv := ε • e.inv
  hom_inv_id := by
    rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, e.hom_inv_id]
  inv_hom_id := by
    rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, e.inv_hom_id]

end CategoryTheory

namespace CategoryTheory.Limits

universe w

/-- An endomorphism `E` of the point of a colimit cocone `c` fixes every map `φ : c.pt ⟶ W`
invariant under a family of endomorphisms `ρ i`, as soon as, restricted to every leg `c.ι j`,
`E` is an average of some of the `ρ i`: for a finite family `σ : κ → ι` with `|κ|` invertible
on `W`, the sum of `|κ|` copies of `c.ι j ≫ E` is `∑ k, c.ι j ≫ ρ (σ k)`. -/
lemma IsColimit.comp_eq_of_sum_const_comp_eq_sum {C J : Type*} [Category C] [Preadditive C]
    [Category J] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {ι : Type*} (E : c.pt ⟶ c.pt)
    (ρ : ι → (c.pt ⟶ c.pt)) {W : C} (φ : c.pt ⟶ W) (hφ : ∀ i, ρ i ≫ φ = φ)
    (havg : ∀ j, ∃ (κ : Type w) (_ : Fintype κ) (σ : κ → ι), IsIso (Fintype.card κ • 𝟙 W) ∧
      ∑ _k : κ, c.ι.app j ≫ E = ∑ k, c.ι.app j ≫ ρ (σ k)) :
    E ≫ φ = φ := by
  refine hc.hom_ext fun j ↦ ?_
  obtain ⟨κ, _, σ, hW, h⟩ := havg j
  have h' := congrArg (· ≫ φ) h
  simp only [Preadditive.sum_comp, Preadditive.nsmul_comp, Category.assoc, hφ, Finset.sum_const,
    Finset.card_univ] at h'
  rw [← cancel_mono (Fintype.card κ • 𝟙 W)]
  simpa only [Preadditive.comp_nsmul, Category.comp_id, Category.assoc] using h'

end CategoryTheory.Limits
