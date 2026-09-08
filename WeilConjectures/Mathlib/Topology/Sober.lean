/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Sober

/-!
# Generic points of the irreducible components

Some basic facts about `genericPoints α`, the set of generic points of the irreducible components
of a topological space `α`: distinct generic points do not lie in each other's closure
(`genericPoints.notMem_closure_of_ne`), any set containing all of them is dense
(`genericPoints.dense_of_subset`), and hence the intersection of a finite family of open sets
each containing all of them is a dense open (`genericPoints.dense_iInf_of_subset`).

`genericPoints.notMem_closure_of_ne` holds because otherwise the irreducible component of `x`
would be contained in the irreducible component of `y`, hence equal to it by maximality.
-/

@[expose] public section

variable {α : Type*} [TopologicalSpace α]

namespace genericPoints

/-- If `x` and `y` are distinct generic points of irreducible components, then `x` does not lie
in the closure of `y`. -/
theorem notMem_closure_of_ne [T0Space α] {x y : α} (hx : x ∈ genericPoints α)
    (hy : y ∈ genericPoints α) (hxy : x ≠ y) : x ∉ _root_.closure ({y} : Set α) := by
  intro hmem
  have hle : _root_.closure ({x} : Set α) ⊆ _root_.closure ({y} : Set α) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  exact hxy (isGenericPoint_closure.eq (hle.antisymm (hx.2 hy.1 hle)).symm)

/-- The generic points of the irreducible components are dense. -/
theorem dense [QuasiSober α] : Dense (genericPoints α) :=
  dense_iff_closure_eq.mpr genericPoints.closure

/-- A set containing all generic points of the irreducible components is dense. -/
theorem dense_of_subset [QuasiSober α] {s : Set α} (h : genericPoints α ⊆ s) : Dense s :=
  dense.mono h

/-- The intersection of a finite family of open sets each of which contains all the generic
points of the irreducible components is dense. -/
theorem dense_iInf_of_subset [QuasiSober α] {ι : Type*} [Finite ι]
    {U : ι → TopologicalSpace.Opens α} (h : ∀ i, genericPoints α ⊆ (U i : Set α)) :
    Dense ((⨅ i, U i : TopologicalSpace.Opens α) : Set α) :=
  dense_of_subset <| by
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.subset_iInter h

end genericPoints
