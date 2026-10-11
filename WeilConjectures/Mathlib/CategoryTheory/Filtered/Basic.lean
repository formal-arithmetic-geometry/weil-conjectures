/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite families of morphisms in a filtered category

In a filtered category, finitely many objects admit a common target, and finitely many
morphisms `f a : j ⟶ k a` out of a common source can be completed to a commuting cocone.
-/

@[expose] public section

namespace CategoryTheory.IsFiltered

variable {C : Type*} [Category* C] [IsFiltered C]

/-- In a filtered category, finitely many objects admit morphisms to a common object. -/
lemma exists_forall_nonempty_hom {ι : Type*} [Finite ι] (k : ι → C) :
    ∃ m : C, ∀ a, Nonempty (k a ⟶ m) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨m, hm⟩ := sup_objs_exists (Finset.univ.image k)
  exact ⟨m, fun a ↦ hm (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩

/-- In a filtered category, finitely many morphisms `f a : j ⟶ k a` out of a common source can
be completed to a commuting cocone: there are `g : j ⟶ m` and `h a : k a ⟶ m` with
`f a ≫ h a = g` for all `a`. -/
lemma exists_forall_comp_eq {ι : Type*} [Finite ι] {j : C} (k : ι → C) (f : ∀ a, j ⟶ k a) :
    ∃ (m : C) (g : j ⟶ m) (h : ∀ a, k a ⟶ m), ∀ a, f a ≫ h a = g := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset C := insert j (Finset.univ.image k)
  have hj : j ∈ O := Finset.mem_insert_self _ _
  have hk (a : ι) : k a ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun a ↦ ⟨j, k a, hj, hk a, f a⟩
  exact ⟨sup O H, toSup O H hj, fun a ↦ toSup O H (hk a), fun a ↦
    toSup_commutes O H hj (hk a) (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩

end CategoryTheory.IsFiltered
