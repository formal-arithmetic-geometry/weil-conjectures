/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# The constructible topology of a spectral space is Hausdorff

Source: Stacks Project, Topology, Lemma 5.23.2 (Tag 0901), Hausdorff part
(blueprint: lem-weil-pbc-spectral-constructible-topology-hausdorff).
-/

@[expose] public section

universe u

/-- The constructible topology of a spectral space is Hausdorff.
Source: Stacks Project, Topology, Lemma 5.23.2 (Tag 0901), first paragraph of the proof
(blueprint: lem-weil-pbc-spectral-constructible-topology-hausdorff).

Proof outline:
1. For distinct points `x` and `y`, sobriety supplies an open set containing exactly one of
   them (`def-weil-spectral-space`). Indeed, their singleton closures are irreducible closed
   sets (`def-weil-irreducible-components`, `lem-weil-pbc-irreducible-closure`). If both points
   specialize to each other, these closures agree and have two generic points, contradicting
   uniqueness. After exchanging the points if necessary, take the complement of the closure
   of `y` as an open neighbourhood of `x` missing `y`.
2. The basis of quasi-compact opens (`def-weil-spectral-space`) gives a quasi-compact open `U`
   containing `x` inside that neighbourhood, so `y` is outside `U`.
3. Both `U` and its complement are subbasic opens in the constructible topology
   (`def-weil-pbc-constructible-topology`). They are disjoint neighbourhoods of `x` and `y`.
   Exchange the two neighbourhoods back if the points were exchanged in step 1. -/
theorem t2Space_constructibleTopology (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    @T2Space X (constructibleTopology X) := by
  sorry
