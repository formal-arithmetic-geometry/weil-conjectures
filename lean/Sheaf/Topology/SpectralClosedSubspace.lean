/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Topology.Spectral.Basic

/-!
# Closed subspaces of spectral spaces

Source: Stacks Project, Topology, Tag 0902, the closed-subset case
(blueprint: lem-weil-pbc-spectral-closed-subspace).
-/

@[expose] public section

universe u

namespace Topology

/-- A closed subspace of a spectral space is spectral, and its compact opens are precisely
traces of ambient compact opens. Source: Stacks Project, Topology, Tag 0902, closed-subset case
(blueprint: lem-weil-pbc-spectral-closed-subspace).

Proof: (1) Closed subspaces inherit sobriety (lem-weil-pbc-closed-subspace-sober).
(2) They inherit compactness (lem-weil-pbc-closed-in-quasi-compact).
(3) A trace of an ambient compact open is open in the subtype and closed in that compact open,
so compact by lem-weil-pbc-closed-in-quasi-compact. The induced topologies agree.
(4) Cover any compact open of the subtype by traces of ambient basis compact opens, then take
finitely many using compactness. Their finite union is an ambient compact open with that trace.
(5) The traces form a basis, by the ambient basis property.
(6) Intersections of two compact opens are compact: express both as traces, intersect their
ambient compact opens, and apply (3), using ambient quasi-separatedness.
(7) Sobriety, compactness, this basis and quasi-separatedness give spectrality by
 def-weil-spectral-space. Steps (3) and (4) give the asserted equivalence. -/
theorem spectral_closed_subspace {X : Type u} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X) (hE : IsClosed E) :
    SpectralSpace E ∧
      ∀ V : Set E, (IsOpen V ∧ IsCompact V) ↔
        ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ V = Subtype.val ⁻¹' U := by
  sorry

end Topology
