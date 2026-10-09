/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Constructible sets of spectral spaces are quasi-compact

In a quasi-compact, quasi-separated, quasi-sober prespectral space `X` (for instance a spectral
space), every constructible set is quasi-compact. Indeed, constructible sets are closed in the
constructible topology, which is quasi-compact (`compactSpace_withConstructibleTopology`) and
finer than the topology of `X`.

## Main statements

- `constructibleTopology_le`: the constructible topology of a prespectral space is finer than
  its topology.
- `Topology.IsConstructible.isCompact`: constructible sets are quasi-compact.
-/

@[expose] public section

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The constructible topology of a prespectral space is finer than its topology: an open set is
a union of quasi-compact open sets, which are open in the constructible topology. -/
lemma constructibleTopology_le [PrespectralSpace X] :
    constructibleTopology X ≤ ‹TopologicalSpace X› := by
  intro U hU
  rw [PrespectralSpace.isTopologicalBasis.open_eq_sUnion' hU]
  refine @isOpen_sUnion X (constructibleTopology X) _ fun V hV ↦ ?_
  exact hV.1.2.isOpen_constructibleTopology_of_isOpen hV.1.1

/-- A constructible set is clopen in the constructible topology, in a quasi-compact space. -/
lemma Topology.IsConstructible.isClopen_constructibleTopology [CompactSpace X] {s : Set X}
    (hs : IsConstructible s) : @IsClopen X (constructibleTopology X) s := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU hU' =>
    refine ⟨?_, hU'.isCompact.isOpen_constructibleTopology_of_isOpen hU⟩
    refine (@isOpen_compl_iff X U (constructibleTopology X)).mp ?_
    exact (by rw [compl_compl]; exact hU'.isCompact : IsCompact Uᶜᶜ
      ).isOpen_constructibleTopology_of_isClosed hU.isClosed_compl
  | union s _ t _ hs ht => exact @IsClopen.union X (constructibleTopology X) _ _ hs ht
  | compl s _ hs => exact @IsClopen.compl X (constructibleTopology X) _ hs

/-- **Constructible sets are quasi-compact** in a quasi-compact, quasi-separated, quasi-sober
prespectral space: they are closed in the constructible topology, which is quasi-compact and
finer than the topology of `X`. -/
lemma Topology.IsConstructible.isCompact [CompactSpace X] [QuasiSober X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] {s : Set X} (hs : IsConstructible s) : IsCompact s := by
  let φ : WithConstructibleTopology X → X := WithTopology.ofTopology
  have hφ : Continuous φ := by
    refine continuous_def.mpr fun U hU ↦ ?_
    rw [WithConstructibleTopology.isOpen_iff]
    exact constructibleTopology_le U hU
  have hK : IsClosed (φ ⁻¹' s) := by
    rw [WithConstructibleTopology.isClosed_iff]
    exact hs.isClopen_constructibleTopology.1
  have := hK.isCompact.image hφ
  rwa [Set.image_preimage_eq _ fun x ↦ ⟨WithTopology.toTopology _ x, rfl⟩] at this
