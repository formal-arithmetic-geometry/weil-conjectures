/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Attaining finitely many conditions jointly by refining an object

Finitely many conditions on the objects over a fixed object `j₂`, each of them stable
under further refinement and each of them individually attainable below any object, can be
attained jointly (`CategoryTheory.exists_hom_forall`). The intended use is in a cofiltered
category, where the individual conditions are attainable by the cofiltering property, but
no assumption on the category is needed for the induction itself.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

/-- **Finitely many refinement conditions can be met simultaneously.** Let `P j k l` be a
family of conditions on the objects `j` over a fixed object `j₂`, indexed by a finite type
`ι`. If every condition is stable under precomposition with a further refinement, and
every single condition can be met below any object, then all of them can be met below
`j₂` at once. -/
lemma exists_hom_forall {ι : Type*} [Finite ι] {j₂ : J}
    (P : ∀ j : J, (j ⟶ j₂) → ι → Prop)
    (hstab : ∀ {j j' : J} (k' : j' ⟶ j) (k : j ⟶ j₂) (l : ι), P j k l → P j' (k' ≫ k) l)
    (hex : ∀ (j : J) (k : j ⟶ j₂) (l : ι), ∃ (j' : J) (k' : j' ⟶ j), P j' (k' ≫ k) l) :
    ∃ (j : J) (k : j ⟶ j₂), ∀ l, P j k l := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ (j : J) (k : j ⟶ j₂), ∀ l ∈ s, P j k l by
    obtain ⟨j, k, hj⟩ := h Finset.univ
    exact ⟨j, k, fun l ↦ hj l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨j₂, 𝟙 j₂, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, k, hj⟩ := ih
    obtain ⟨j', k', hj'⟩ := hex j k a
    refine ⟨j', k' ≫ k, fun l hl ↦ ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj'
    · exact hstab k' k l (hj l hl)

end CategoryTheory
