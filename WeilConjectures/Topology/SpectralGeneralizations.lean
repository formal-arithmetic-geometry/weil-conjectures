/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic

/-!
# Generalizations of quasi-compact subsets in spectral spaces

In a spectral space, the set of generalizations of a quasi-compact set is quasi-compact and is
the intersection of all quasi-compact opens containing that set.

## References

* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31), proof of (3) ⇒ (4)
-/

@[expose] public section

universe u

open Set Topology

namespace Topology

/-- In a spectral space, the generalizations of a quasi-compact set are quasi-compact and
are the intersection of all quasi-compact opens containing that set. -/
theorem generalizations_isCompact_sInter_isCompactOpen
    (X : Type u) [TopologicalSpace X] [SpectralSpace X]
    (E : Set X) (hE : IsCompact E) :
    IsCompact {x : X | closure ({x} : Set X) ∩ E ≠ ∅} ∧
      {x : X | closure ({x} : Set X) ∩ E ≠ ∅} =
        ⋂₀ {U : Set X | IsOpen U ∧ IsCompact U ∧ E ⊆ U} := by
  classical
  let W : Set X := {x : X | closure ({x} : Set X) ∩ E ≠ ∅}
  have hEW : E ⊆ W := by
    intro e he
    exact Set.nonempty_iff_ne_empty.mp ⟨e, subset_closure (mem_singleton e), he⟩
  have hWU : ∀ U : Set X, IsOpen U → E ⊆ U → W ⊆ U := by
    intro U hU hEU w hw
    obtain ⟨e, hew, heE⟩ := Set.nonempty_iff_ne_empty.mpr hw
    exact (specializes_iff_mem_closure.mpr hew).mem_open hU (hEU heE)
  have hW : IsCompact W := by
    apply isCompact_of_finite_subcover
    intro ι U hU hcover
    obtain ⟨t, ht⟩ := hE.elim_finite_subcover U hU (hEW.trans hcover)
    exact ⟨t, hWU _ (isOpen_biUnion fun i _ => hU i) ht⟩
  refine ⟨hW, subset_antisymm ?_ ?_⟩
  · intro x hx U hU
    exact hWU U hU.1 hU.2.2 hx
  · intro x hx
    by_contra hxW
    have hWZ : W ⊆ (closure ({x} : Set X))ᶜ := by
      intro w hw hwZ
      obtain ⟨e, hew, heE⟩ := Set.nonempty_iff_ne_empty.mpr hw
      have hxe : e ∈ closure ({x} : Set X) :=
        ((specializes_iff_mem_closure.mpr hwZ).trans
          (specializes_iff_mem_closure.mpr hew)).mem_closure
      exact hxW (Set.nonempty_iff_ne_empty.mp ⟨e, hxe, heE⟩)
    obtain ⟨U, hUc, hUo, hWU', hUZ⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between hW
        isClosed_closure.isOpen_compl hWZ
    exact hUZ (hx U ⟨hUo, hUc, hEW.trans hWU'⟩)
      (subset_closure (mem_singleton x))

end Topology
