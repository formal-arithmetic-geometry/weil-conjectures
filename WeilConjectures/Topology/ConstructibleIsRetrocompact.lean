/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible

/-!
# Constructible subsets are retrocompact

## References

* Stacks Project, Tag 09YH.
-/

@[expose] public section

universe u

namespace Topology

/-- Every constructible subset of a topological space is retrocompact. -/
theorem IsConstructible.isRetrocompact {X : Type u} [TopologicalSpace X] {E : Set X}
    (hE : IsConstructible E) : IsRetrocompact E := by
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, IsRetrocompact.empty⟩
  | top_mem => exact ⟨isOpen_univ, IsRetrocompact.univ⟩
  | sdiff U hU V hV =>
    intro W hWcomp hWopen
    simpa only [Set.sdiff_eq, Set.inter_right_comm] using (hU.2 hWcomp hWopen).diff hV.1
  | sup s _ t _ hs ht => exact hs.union ht

end Topology
