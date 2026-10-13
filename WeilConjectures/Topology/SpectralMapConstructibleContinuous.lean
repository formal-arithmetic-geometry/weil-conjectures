/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Hom

/-!
# Spectral maps are continuous for the constructible topologies

Source: Stacks Project, Topology, Lemma 5.23.3, Tag 0A2S, part (1)
(blueprint: lem-weil-pbc-spectral-map-constructible-continuous).
-/

@[expose] public section

universe u v

/-- A spectral map of spectral spaces is continuous for their constructible topologies.
Source: Stacks Project, Topology, Lemma 5.23.3, Tag 0A2S, part (1).
(blueprint: lem-weil-pbc-spectral-map-constructible-continuous)

Proof: For a quasi-compact open `W` in the target, its preimage is open by continuity
and quasi-compact by the spectral-map hypothesis, hence open in the constructible topology
of the source (`def-weil-pbc-constructible-topology`). The preimage of the complement of `W`
is the complement of this quasi-compact open preimage, hence also subbasic and open in the
constructible topology. These two cases cover the subbasis of the target's constructible
topology, so the subbasis criterion (`lem-weil-pbc-continuous-iff-subbase`) gives continuity.
Equivalently, the preimage of every constructibly open subset of the target is constructibly
open in the source. -/
theorem IsSpectralMap.continuous_constructibleTopology
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SpectralSpace X] [SpectralSpace Y] {f : X → Y} (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f := by
  sorry
