/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Finite closed subsets of a Jacobson space

In a Jacobson space the closed points are dense in every closed subset. If the closed subset
is moreover finite, density forces it to consist of closed points.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- Every point of a finite closed subset of a Jacobson space is a closed point. -/
lemma Set.Finite.subset_closedPoints [JacobsonSpace X] {s : Set X} (hs : s.Finite)
    (hs' : IsClosed s) : s ⊆ closedPoints X := by
  intro x hx
  have hcl : closure {x} ⊆ s := hs'.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have hfin : (closure {x} ∩ closedPoints X).Finite :=
    (hs.subset hcl).subset Set.inter_subset_left
  have hclosed : IsClosed (closure {x} ∩ closedPoints X) := by
    rw [← (closure {x} ∩ closedPoints X).biUnion_of_singleton]
    exact hfin.isClosed_biUnion fun _ hy ↦ hy.2
  have key := JacobsonSpace.closure_inter_closedPoints (X := X) (Z := closure {x}) isClosed_closure
  rw [hclosed.closure_eq] at key
  exact (key.ge (subset_closure (Set.mem_singleton x))).2
