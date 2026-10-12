/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible

/-!
# Constructible sets are retrocompact

In an arbitrary topological space, every constructible set is retrocompact
(Stacks, Topology, Lemma 09YH).

## Main statements

- `Topology.IsConstructible.isRetrocompact`: a constructible set is retrocompact.
-/

@[expose] public section

open Set

namespace Topology

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- A constructible subset of a topological space is retrocompact: its intersection with every
quasi-compact open is quasi-compact. No separation axiom is needed.
(blueprint: `lem-weil-pbc-constructible-is-retrocompact`) -/
theorem IsConstructible.isRetrocompact (hs : IsConstructible s) : IsRetrocompact s := by
  have hlat : IsSublattice {U : Set X | IsOpen U ∧ IsRetrocompact U} :=
    ⟨fun _ hU _ hV ↦ ⟨hU.1.union hV.1, hU.2.union hV.2⟩,
      fun _ hU _ hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_isOpen hV.2 hV.1⟩⟩
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction hlat
    ⟨isOpen_empty, .empty⟩ ⟨isOpen_univ, .univ⟩ with
  | sdiff U hU V hV =>
    intro W hWcomp hWopen
    have h := (hU.2 hWcomp hWopen).diff hV.1
    rwa [Set.sdiff_eq, Set.inter_right_comm, ← Set.sdiff_eq] at h
  | sup s _ t _ hs ht => exact hs.union ht

end Topology
