/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Finite closed subsets of Jacobson spaces

In a Jacobson space every point of a finite closed subset is closed: the closure of such a
point is a finite closed set, and the closed points are dense in it.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- In a Jacobson space, every point of a finite closed subset is a closed point. -/
lemma isClosed_singleton_of_mem_of_finite [JacobsonSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hZf : Z.Finite) {x : X} (hx : x ∈ Z) : IsClosed {x} := by
  have hsub : closure {x} ⊆ Z := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
  have hfin : (closure {x} ∩ closedPoints X).Finite := (hZf.subset hsub).inter_of_left _
  have hcl : IsClosed (closure {x} ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closure {x} ∩ closedPoints X)]
    exact hfin.isClosed_biUnion fun y hy ↦ hy.2
  have h := JacobsonSpace.closure_inter_closedPoints_eq_closure
    (isClosed_closure (s := ({x} : Set X))).isLocallyClosed
  rw [hcl.closure_eq, closure_closure] at h
  have hxm : x ∈ closure {x} ∩ closedPoints X := by
    rw [h]
    exact subset_closure rfl
  exact hxm.2
