/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.LocallyClosed
public import WeilConjectures.Mathlib.Topology.Closure
public import WeilConjectures.Mathlib.Topology.GDelta.Basic

/-!
# Nowhere density of locally closed subsets

A locally closed subset is nowhere dense as soon as its interior is empty
(`IsLocallyClosed.isNowhereDense_iff`), generalising `IsClosed.isNowhereDense_iff`. Hence a
locally closed subset minus its interior is nowhere dense
(`IsLocallyClosed.isNowhereDense_sdiff_interior`), and for a finite cover of a topological
space by locally closed subsets the union of the interiors is dense
(`dense_iUnion_interior_of_isLocallyClosed`). No Noetherian hypothesis is needed.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- **A locally closed subset is nowhere dense if and only if its interior is empty**:
writing `s = coborder s ∩ closure s` with `coborder s` open, the open set
`interior (closure s)` meets `coborder s` inside `interior s = ∅`, and an open subset of
`closure (coborder s)` disjoint from `coborder s` is empty. This generalises
`IsClosed.isNowhereDense_iff`. -/
lemma IsLocallyClosed.isNowhereDense_iff {s : Set X} (hs : IsLocallyClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  refine ⟨fun h ↦ Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans h.le),
    fun h ↦ ?_⟩
  have hopen : IsOpen (coborder s) := hs.isOpen_coborder
  have h₁ : interior (closure s) ∩ coborder s = ∅ := by
    rw [← hopen.interior_eq, ← interior_inter, Set.inter_comm (closure s) (coborder s),
      coborder_inter_closure, h]
  have h₂ : interior (closure s) ⊆ closure (coborder s) :=
    interior_subset.trans (closure_mono subset_coborder)
  rw [IsNowhereDense]
  apply Set.eq_empty_of_subset_empty
  calc interior (closure s) = interior (closure s) ∩ closure (coborder s) :=
        (Set.inter_eq_left.mpr h₂).symm
    _ ⊆ closure (interior (closure s) ∩ coborder s) := isOpen_interior.inter_closure
    _ = ∅ := by rw [h₁, closure_empty]

/-- A locally closed subset minus its interior is nowhere dense. -/
lemma IsLocallyClosed.isNowhereDense_sdiff_interior {s : Set X} (hs : IsLocallyClosed s) :
    IsNowhereDense (s \ interior s) :=
  (hs.inter isOpen_interior.isClosed_compl.isLocallyClosed).isNowhereDense_iff.mpr
    (interior_sdiff_interior s)

/-- **For a finite cover of a topological space by locally closed subsets, the union of the
interiors is dense**: the complement of the union of the interiors is contained in the union
of the nowhere dense sets `sᵢ \ interior sᵢ`. -/
theorem dense_iUnion_interior_of_isLocallyClosed {ι : Type*} [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsLocallyClosed (f i)) (hcov : ⋃ i, f i = Set.univ) :
    Dense (⋃ i, interior (f i)) := by
  have hN : IsNowhereDense (⋃ i, f i \ interior (f i)) :=
    isNowhereDense_iUnion fun i ↦ (hf i).isNowhereDense_sdiff_interior
  have hint : interior (⋃ i, f i \ interior (f i)) = ∅ :=
    Set.eq_empty_of_subset_empty ((interior_mono subset_closure).trans hN.le)
  refine (interior_eq_empty_iff_dense_compl.mp hint).mono fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  by_contra hxi
  exact hx (Set.mem_iUnion.mpr ⟨i, hi, hxi⟩)
