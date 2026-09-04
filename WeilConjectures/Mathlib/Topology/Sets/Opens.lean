/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Compactness of a finite supremum of opens

A finite supremum of compact opens of a topological space is compact
(`TopologicalSpace.Opens.isCompact_finset_sup`).
-/

@[expose] public section

namespace TopologicalSpace.Opens

variable {ι X : Type*} [TopologicalSpace X]

/-- A finite supremum of compact opens is compact. -/
lemma isCompact_finset_sup (s : Finset ι) {U : ι → Opens X}
    (hU : ∀ i ∈ s, IsCompact (U i : Set X)) : IsCompact ((s.sup U : Opens X) : Set X) := by
  rw [coe_finset_sup, Finset.sup_eq_iSup]
  exact s.isCompact_biUnion hU

end TopologicalSpace.Opens
