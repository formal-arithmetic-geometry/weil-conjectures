/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Attaining finitely many conditions jointly by refining an object

Finitely many conditions on the objects over a fixed object `i`, each of them stable
under further refinement and each of them individually attainable below any object, can be
attained jointly
(`CategoryTheory.exists_hom_forall_of_stableUnderPrecomp_of_forall_exists_hom`). The
intended use is in a cofiltered category, where the individual conditions are attainable by
the cofiltering property, but no assumption on the category is needed for the induction
itself.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

/-- **Finitely many refinement conditions can be met simultaneously.** Let `P j k l` be a
family of conditions on the objects `j` over a fixed object `i`, indexed by a finite type
`ι`. If every condition is stable under precomposition with a further refinement, and
every single condition can be met below any object, then all of them can be met below
`i` at once. -/
lemma exists_hom_forall_of_stableUnderPrecomp_of_forall_exists_hom
    {ι : Type*} [Finite ι] {i : J}
    (P : ∀ j : J, (j ⟶ i) → ι → Prop)
    (hstab : ∀ {j j' : J} (k' : j' ⟶ j) (k : j ⟶ i) (l : ι), P j k l → P j' (k' ≫ k) l)
    (hex : ∀ (j : J) (k : j ⟶ i) (l : ι), ∃ (j' : J) (k' : j' ⟶ j), P j' (k' ≫ k) l) :
    ∃ (j : J) (k : j ⟶ i), ∀ l, P j k l := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ (j : J) (k : j ⟶ i), ∀ l ∈ s, P j k l by
    obtain ⟨j, k, hj⟩ := h Finset.univ
    exact ⟨j, k, fun l ↦ hj l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | insert a s ha ih =>
    obtain ⟨j, k, hj⟩ := ih
    obtain ⟨j', k', hj'⟩ := hex j k a
    refine ⟨j', k' ≫ k, fun l hl ↦ ?_⟩
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact hj'
    · exact hstab k' k l (hj l hl)

end CategoryTheory
