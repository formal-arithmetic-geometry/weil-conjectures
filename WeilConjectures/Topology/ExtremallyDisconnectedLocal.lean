/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Topology.Constructible

/-!
# Local criteria for extremally disconnected spaces

## Main results

- `ExtremallyDisconnected.of_forall_exists_injOn`: a space admitting a continuous map to an
  extremally disconnected space which is, locally on the source, injective and open, is
  extremally disconnected.
- `Topology.IsConstructible.isClopen`: in a compact Hausdorff space every constructible set is
  clopen.
- `Topology.IsConstructible.isClopen_preimage_val`: the trace of a constructible set on a closed
  Hausdorff subspace of a compact space is clopen.
-/

@[expose] public section

open Set Topology

/-- Let `f : X → Y` be continuous with `Y` extremally disconnected. If every point of `X` has an
open neighbourhood `U` on which `f` is injective and which `f` maps open subsets of to open
subsets, then `X` is extremally disconnected.

For `V` open in `X` and `z ∈ closure V` with such a neighbourhood `U`, the open set
`U ∩ f⁻¹ (closure (f (U ∩ V)))` contains `z` and is contained in `closure V`. -/
theorem ExtremallyDisconnected.of_forall_exists_injOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ExtremallyDisconnected Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U ∧
      ∀ V ⊆ U, IsOpen V → IsOpen (f '' V)) :
    ExtremallyDisconnected X where
  open_closure V hV := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hU, hzU, hinj, hopen⟩ := h z
    refine ⟨U ∩ f ⁻¹' closure (f '' (U ∩ V)), ?_, ?_, hzU, ?_⟩
    · rintro w ⟨hwU, hw⟩
      rw [mem_closure_iff_nhds]
      intro N hN
      obtain ⟨O, hON, hO, hwO⟩ := mem_nhds_iff.1 hN
      obtain ⟨_, ⟨a, ha, rfl⟩, v, hv, hva⟩ := mem_closure_iff.1 hw _
        (hopen _ inter_subset_right (hO.inter hU)) ⟨w, ⟨hwO, hwU⟩, rfl⟩
      have hav : v = a := hinj hv.1 ha.2 hva
      exact ⟨v, hON (hav ▸ ha.1), hv.2⟩
    · exact hU.inter ((ExtremallyDisconnected.open_closure _
        (hopen _ inter_subset_left (hU.inter hV))).preimage hf)
    · exact image_closure_subset_closure_image hf ⟨z, hU.inter_closure ⟨hzU, hz⟩, rfl⟩

/-- In a compact Hausdorff space every constructible set is clopen: open retrocompact sets are
compact, hence closed, and clopen sets are stable under finite unions and complements. -/
theorem Topology.IsConstructible.isClopen {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {s : Set X} (hs : IsConstructible s) : IsClopen s := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU hUc => exact ⟨hUc.isCompact.isClosed, hU⟩
  | union s _ t _ hs ht => exact hs.union ht
  | compl s _ hs => exact hs.compl

/-- Let `T` be a closed subset of a compact space `X` which is Hausdorff in the subspace topology.
The trace on `T` of a constructible subset of `X` is clopen in `T`: the trace of an open
retrocompact set is open and compact, hence closed. -/
theorem Topology.IsConstructible.isClopen_preimage_val {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {T : Set X} (hT : IsClosed T) [T2Space T] {s : Set X}
    (hs : IsConstructible s) : IsClopen ((↑) ⁻¹' s : Set T) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU hUc =>
    exact ⟨(hT.isClosedEmbedding_subtypeVal.isCompact_preimage hUc.isCompact).isClosed,
      hU.preimage continuous_subtype_val⟩
  | union s _ t _ hs ht => exact preimage_union (f := ((↑) : T → X)) ▸ hs.union ht
  | compl s _ hs => exact preimage_compl (f := ((↑) : T → X)) ▸ hs.compl
