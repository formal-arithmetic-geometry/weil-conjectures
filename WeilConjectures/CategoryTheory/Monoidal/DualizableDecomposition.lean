/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition

/-!
# Finite direct sums of dualizable objects

In a preadditive monoidal category `C` whose tensor product is additive, an object `P` which is a
finite direct sum of objects `Sⱼ` with right duals, in the sense of inclusions `Sⱼ ⟶ P` and
projections `P ⟶ Sⱼ` with `∑ⱼ projⱼ ≫ inclⱼ = 𝟙 P` and `inclⱼ ≫ projⱼ' = δⱼⱼ'`, has a right
dual: the biproduct `⨁ⱼ Sⱼᘁ` of the duals
(`CategoryTheory.nonempty_hasRightDual_of_decomposition`). The evaluation and coevaluation are
the sums of those of the summands.

In particular an object with a decomposition `P ≅ ⨁ⱼ E⟦nⱼ⟧` into shifts of an object `E` all of
whose shifts are dualizable is dualizable (`CategoryTheory.ShiftDecomposition.isDualizable`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- **A finite direct sum of objects with right duals has a right dual.** If `P` is the direct
sum of a finite family `Sⱼ` of objects with right duals, through inclusions `inclⱼ : Sⱼ ⟶ P` and
projections `projⱼ : P ⟶ Sⱼ`, then `P` has the right dual `⨁ⱼ Sⱼᘁ`, with coevaluation
`∑ⱼ η_{Sⱼ} ≫ (inclⱼ ⊗ ιⱼ)` and evaluation `∑ⱼ (πⱼ ⊗ projⱼ) ≫ ε_{Sⱼ}`. -/
theorem nonempty_hasRightDual_of_decomposition {ι : Type} [Fintype ι]
    {S : ι → C} [∀ j, HasRightDual (S j)] [HasBiproduct fun j ↦ (S j)ᘁ] {P : C}
    (incl : ∀ j, S j ⟶ P) (proj : ∀ j, P ⟶ S j) (total : ∑ j, proj j ≫ incl j = 𝟙 P)
    (incl_proj_self : ∀ j, incl j ≫ proj j = 𝟙 _)
    (incl_proj_of_ne : ∀ j j', j ≠ j' → incl j ≫ proj j' = 0) :
    Nonempty (HasRightDual P) := by
  classical
  let Q := ⨁ fun j ↦ (S j)ᘁ
  let a : ι → (𝟙_ C ⟶ P ⊗ Q) := fun j ↦
    η_ (S j) (S j)ᘁ ≫ (incl j ⊗ₘ biproduct.ι (fun j ↦ (S j)ᘁ) j)
  let b : ι → (Q ⊗ P ⟶ 𝟙_ C) := fun j ↦
    (biproduct.π (fun j ↦ (S j)ᘁ) j ⊗ₘ proj j) ≫ ε_ (S j) (S j)ᘁ
  have h₁ (j j' : ι) : Q ◁ a j ≫ (α_ Q P Q).inv ≫ b j' ▷ Q =
      if j = j' then (ρ_ Q).hom ≫ biproduct.π (fun j ↦ (S j)ᘁ) j ≫
        biproduct.ι (fun j ↦ (S j)ᘁ) j ≫ (λ_ Q).inv else 0 := by
    simp only [a, b]
    rw [whiskerLeft_coevaluation_evaluation]
    split_ifs with h
    · subst h
      rw [incl_proj_self, MonoidalCategory.whiskerLeft_id, id_whiskerRight, Category.id_comp,
        ExactPairing.coevaluation_evaluation_assoc, rightUnitor_naturality_assoc,
        ← leftUnitor_inv_naturality]
    · rw [incl_proj_of_ne j j' h, MonoidalPreadditive.whiskerLeft_zero,
        MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, comp_zero, comp_zero]
  have h₂ (j j' : ι) : a j ▷ P ≫ (α_ P Q P).hom ≫ P ◁ b j' =
      if j = j' then (λ_ P).hom ≫ proj j ≫ incl j ≫ (ρ_ P).inv else 0 := by
    simp only [a, b]
    rw [whiskerRight_coevaluation_evaluation]
    split_ifs with h
    · subst h
      rw [biproduct.ι_π_self, id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp,
        ← leftUnitor_naturality_assoc, ExactPairing.evaluation_coevaluation_assoc,
        rightUnitor_inv_naturality]
    · rw [biproduct.ι_π_ne _ h, MonoidalPreadditive.zero_whiskerRight,
        MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero, comp_zero, comp_zero]
  exact ⟨
    { rightDual := Q
      exact :=
        { coevaluation' := ∑ j, a j
          evaluation' := ∑ j, b j
          coevaluation_evaluation' := by
            simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp,
              Preadditive.comp_sum, h₁, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
            rw [← Preadditive.comp_sum]
            simp only [← Category.assoc, ← Preadditive.sum_comp]
            rw [biproduct.total, Category.comp_id]
          evaluation_coevaluation' := by
            simp only [whiskerLeft_sum, sum_whiskerRight, Preadditive.sum_comp,
              Preadditive.comp_sum, h₂, Finset.sum_ite_eq',
              Finset.mem_univ, if_true]
            rw [← Preadditive.comp_sum]
            simp only [← Category.assoc, ← Preadditive.sum_comp]
            rw [total, Category.comp_id] } }⟩

/-- A finite direct sum of dualizable objects is dualizable. -/
theorem isDualizable_of_decomposition {ι : Type} [Fintype ι] {S : ι → C}
    [HasFiniteBiproducts C] (hS : ∀ j, IsDualizable (S j)) {P : C}
    (incl : ∀ j, S j ⟶ P) (proj : ∀ j, P ⟶ S j) (total : ∑ j, proj j ≫ incl j = 𝟙 P)
    (incl_proj_self : ∀ j, incl j ≫ proj j = 𝟙 _)
    (incl_proj_of_ne : ∀ j j', j ≠ j' → incl j ≫ proj j' = 0) :
    IsDualizable P :=
  letI := fun j ↦ (hS j).some
  nonempty_hasRightDual_of_decomposition incl proj total incl_proj_self incl_proj_of_ne

/-- An object which is a finite direct sum of shifts of an object `E` all of whose shifts are
dualizable is dualizable. -/
theorem ShiftDecomposition.isDualizable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasFiniteBiproducts C] {E P : C} (D : ShiftDecomposition E P)
    (hE : ∀ n : ℤ, IsDualizable ((shiftFunctor C n).obj E)) : IsDualizable P :=
  isDualizable_of_decomposition (fun j ↦ hE (D.deg j)) D.incl D.proj D.total D.incl_proj_self
    D.incl_proj_of_ne

end CategoryTheory
