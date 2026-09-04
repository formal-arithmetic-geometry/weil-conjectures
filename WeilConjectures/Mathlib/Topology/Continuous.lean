/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Continuous

/-!
# Disjoint closures pull back to disjoint closures

`Disjoint.closure_preimage`: if two subsets of the target of a continuous map have disjoint
closures, then the closures of their preimages are disjoint. This is the topological content
of the persistence of disjoint boundary closures along a modification.
-/

@[expose] public section

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {A B : Set Y}

/-- If two subsets have disjoint closures, so do the closures of their preimages under a
continuous map. -/
theorem Disjoint.closure_preimage (h : Disjoint (closure A) (closure B)) (hf : Continuous f) :
    Disjoint (closure (f ⁻¹' A)) (closure (f ⁻¹' B)) :=
  (h.preimage f).mono (hf.closure_preimage_subset A) (hf.closure_preimage_subset B)
