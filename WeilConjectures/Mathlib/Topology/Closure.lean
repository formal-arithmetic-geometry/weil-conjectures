/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Closure

/-!
# The interior of a set minus its interior

`interior_sdiff_interior`: removing the interior of a set kills its interior. This is the
counterpart of `interior_frontier` for a set that is not assumed closed.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- Removing from a set its interior leaves a set with empty interior: such a set is
contained in `interior s` by monotonicity and disjoint from it by construction. -/
@[simp]
lemma interior_sdiff_interior (s : Set X) : interior (s \ interior s) = ∅ :=
  Set.eq_empty_of_subset_empty fun _ hx ↦
    (interior_subset hx).2 (interior_mono Set.sdiff_subset hx)
