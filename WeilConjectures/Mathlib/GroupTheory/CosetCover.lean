/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.CosetCover

/-!
# Avoiding finitely many proper subspaces

Mathlib proves that a vector space over an infinite division ring is not the union of finitely
many proper subspaces, in the form `Subspace.top_mem_of_biUnion_eq_univ`: a finite family of
subspaces whose union is everything contains `⊤`. This file records the form in which that
statement is used, where the subspaces are indexed by a finite set and the conclusion produces a
single vector lying outside all of them.
-/

@[expose] public section

variable {k E ι : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E]

/-- **A vector space over an infinite division ring is not the union of finitely many proper
subspaces**: if each of finitely many subspaces is proper, a single vector avoids all of them. -/
theorem Subspace.exists_forall_notMem {Z : Set ι} (hZ : Z.Finite) (W : ι → Submodule k E)
    (hW : ∀ i ∈ Z, W i ≠ ⊤) : ∃ m : E, ∀ i ∈ Z, m ∉ W i := by
  by_contra h
  push Not at h
  have hcov : ⋃ p ∈ hZ.toFinset.image W, (p : Set E) = Set.univ :=
    Set.eq_univ_of_forall fun m ↦ by
      obtain ⟨i, hi, hm⟩ := h m
      exact Set.mem_biUnion (Finset.mem_image_of_mem W (hZ.mem_toFinset.2 hi)) hm
  obtain ⟨i, hi, hiW⟩ := Finset.mem_image.1 (Subspace.top_mem_of_biUnion_eq_univ hcov)
  exact hW i (hZ.mem_toFinset.1 hi) hiW
