/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Finitely many properties at a common stage of a cofiltered category

If finitely many properties of morphisms `k ⟶ j` into a fixed object `j` of a cofiltered category
each hold for some morphism and are stable under precomposition, then they all hold for a common
morphism (`CategoryTheory.IsCofiltered.exists_forall_of_finite`).
-/

@[expose] public section

namespace CategoryTheory.IsCofiltered

variable {C : Type*} [Category* C] [IsCofiltered C]

/-- Finitely many properties of morphisms into `j`, each of which holds for some morphism into `j`
and is stable under precomposition, hold simultaneously for some morphism into `j`. -/
theorem exists_forall_of_finite {ι : Type*} [Finite ι] {j : C}
    (P : ι → ∀ {k : C}, (k ⟶ j) → Prop)
    (hP : ∀ i {k k' : C} (u : k' ⟶ k) (t : k ⟶ j), P i t → P i (u ≫ t))
    (h : ∀ i, ∃ (k : C) (t : k ⟶ j), P i t) : ∃ (k : C) (t : k ⟶ j), ∀ i, P i t := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : C) (t : k ⟶ j), ∀ i ∈ s, P i t by
    obtain ⟨k, t, hk⟩ := H Finset.univ
    exact ⟨k, t, fun i ↦ hk i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert i s _ ih =>
    obtain ⟨k₁, t₁, h₁⟩ := ih
    obtain ⟨k₂, t₂, h₂⟩ := h i
    let a := minToLeft k₁ k₂ ≫ t₁
    let b := minToRight k₁ k₂ ≫ t₂
    refine ⟨eq a b, eqHom a b ≫ a, fun i' hi' ↦ ?_⟩
    rcases Finset.mem_insert.mp hi' with rfl | hi'
    · rw [eq_condition]
      simpa only [b, Category.assoc] using hP i' (eqHom a b ≫ minToRight k₁ k₂) t₂ h₂
    · simpa only [a, Category.assoc] using hP i' (eqHom a b ≫ minToLeft k₁ k₂) t₁ (h₁ i' hi')

end CategoryTheory.IsCofiltered
