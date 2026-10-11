/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Connected components in a closed subset

## Main statements

- `IsClosed.isClosed_connectedComponentIn`: the connected components of a closed subset are
  closed.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- The connected components of a closed subset `F` are closed: the closure of the connected
component of `x` in `F` is preconnected and contained in `F`. -/
theorem IsClosed.isClosed_connectedComponentIn {F : Set X} (hF : IsClosed F) (x : X) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.1 ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty
