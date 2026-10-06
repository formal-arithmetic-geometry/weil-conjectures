/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Connected components in a closed subset and under inducing maps

The connected component of a point in a closed subset is closed, and an inducing map sends the
connected component of a point onto the connected component of its image in the range.

## Blueprint

- `sk-p-geometry`: the identity component of a closed subgroup of `GL_n`.
-/

@[expose] public section

open Set Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The connected component of a point in a closed subset is closed. -/
theorem IsClosed.connectedComponentIn {F : Set α} (hF : IsClosed F) (x : α) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- An inducing map sends the connected component of `x` onto the connected component of `f x` in
the range of `f`. -/
theorem Topology.IsInducing.image_connectedComponent {f : α → β} (hf : IsInducing f) (x : α) :
    f '' connectedComponent x = connectedComponentIn (range f) (f x) := by
  refine subset_antisymm ((isPreconnected_connectedComponent.image _
    hf.continuous.continuousOn).subset_connectedComponentIn ⟨x, mem_connectedComponent, rfl⟩
    (image_subset_range _ _)) ?_
  have hsub : connectedComponentIn (range f) (f x) ⊆ range f := connectedComponentIn_subset _ _
  rw [← image_preimage_eq_of_subset hsub]
  refine image_mono (IsPreconnected.subset_connectedComponent ?_ ?_)
  · rw [← hf.isPreconnected_image, image_preimage_eq_of_subset hsub]
    exact isPreconnected_connectedComponentIn
  · exact mem_connectedComponentIn (mem_range_self x)
