/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Closure
public import Mathlib.Topology.GDelta.Basic

/-!
# Finite unions of nowhere dense sets

Nowhere density is stable under finite unions: `IsNowhereDense.union`,
`Set.Finite.isNowhereDense_biUnion` and `isNowhereDense_iUnion`.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- The union of two nowhere dense subsets is nowhere dense. -/
lemma IsNowhereDense.union {s t : Set X} (hs : IsNowhereDense s) (ht : IsNowhereDense t) :
    IsNowhereDense (s ∪ t) := by
  rw [IsNowhereDense, closure_union, interior_union_isClosed_of_interior_empty isClosed_closure ht]
  exact hs

/-- A union of nowhere dense subsets indexed by a finite subset of the index type is nowhere
dense. -/
protected lemma Set.Finite.isNowhereDense_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f : ι → Set X} (hf : ∀ i ∈ s, IsNowhereDense (f i)) : IsNowhereDense (⋃ i ∈ s, f i) := by
  revert hf
  induction s, hs using Set.Finite.induction_on with
  | empty => intro _; simp [isNowhereDense_empty]
  | insert ha ht ih =>
    intro hf
    rw [Set.biUnion_insert]
    exact (hf _ (Set.mem_insert _ _)).union (ih fun i hi ↦ hf i (Set.mem_insert_of_mem _ hi))

/-- A union of nowhere dense subsets indexed by a finite type is nowhere dense. -/
lemma isNowhereDense_iUnion {ι : Type*} [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsNowhereDense (f i)) : IsNowhereDense (⋃ i, f i) := by
  simpa using Set.finite_univ.isNowhereDense_biUnion (f := f) fun i _ ↦ hf i
