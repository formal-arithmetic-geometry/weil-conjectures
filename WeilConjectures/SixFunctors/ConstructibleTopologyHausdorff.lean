/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Basic

/-!
# The constructible topology of a spectral space is Hausdorff

The constructible topology of a spectral space is Hausdorff.

## References

* [Stacks, Tag 0901](https://stacks.math.columbia.edu/tag/0901)
-/

@[expose] public section

universe u

/-- The constructible topology of a spectral space is Hausdorff. -/
theorem t2Space_constructibleTopology (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    @T2Space X (constructibleTopology X) := by
  refine @T2Space.mk X (constructibleTopology X) ?_
  intro x y hxy
  obtain ⟨O, hOo, hOxy⟩ := exists_isOpen_xor_mem hxy
  rcases hOxy with ⟨hxO, hyO⟩ | ⟨hyO, hxO⟩
  · obtain ⟨U, ⟨hUo, hUc⟩, hxU, hUO⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxO hOo
    refine ⟨U, Uᶜ, hUc.isOpen_constructibleTopology_of_isOpen hUo,
      (show IsCompact (Uᶜ)ᶜ by simpa using hUc).isOpen_constructibleTopology_of_isClosed
        (s := Uᶜ) (isClosed_compl_iff.mpr hUo), hxU, ?_, Set.disjoint_left.2 ?_⟩
    · intro hyU
      exact hyO (hUO hyU)
    · intro z hzU hzUc
      exact hzUc hzU
  · obtain ⟨U, ⟨hUo, hUc⟩, hyU, hUO⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyO hOo
    refine ⟨Uᶜ, U,
      (show IsCompact (Uᶜ)ᶜ by simpa using hUc).isOpen_constructibleTopology_of_isClosed
        (s := Uᶜ) (isClosed_compl_iff.mpr hUo), hUc.isOpen_constructibleTopology_of_isOpen hUo,
        ?_, hyU, Set.disjoint_left.2 ?_⟩
    · intro hxUc
      exact hxO (hUO hxUc)
    · intro z hzUc hzU
      exact hzUc hzU
