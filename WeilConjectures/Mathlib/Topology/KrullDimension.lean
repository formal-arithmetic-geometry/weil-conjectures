/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Topological Krull dimension and open covers

In a quasi-sober `T₀` space, the coheight of a point is bounded by the topological Krull
dimension, and the topological Krull dimension is bounded by any common bound on the
dimensions of the members of an open cover.

## Main statements

- `coheight_le_topologicalKrullDim`: the coheight of a point for the specialization order is
  at most the topological Krull dimension.
- `topologicalKrullDim_le_of_iSup_eq_top`: the topological Krull dimension is at most any
  common bound on the dimensions of the members of an open cover.
-/

@[expose] public section

open Topology TopologicalSpace Order

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space, the coheight of a point for the specialization order is at
most the topological Krull dimension. -/
theorem coheight_le_topologicalKrullDim {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (x : X) : (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [← coheight_orderIso irreducibleSetEquivPoints.symm]
  exact coheight_le_krullDim _

attribute [local instance] specializationOrder in
/-- The topological Krull dimension of a quasi-sober `T₀` space is bounded by any common
bound on the dimensions of the members of an open cover. -/
theorem topologicalKrullDim_le_of_iSup_eq_top {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {ι : Type*} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) (n : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U i) ≤ n) : topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, krullDim_eq_iSup_coheight]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ (irreducibleSetEquivPoints Z)))
  have := (U i).isOpenEmbedding'.quasiSober
  rw [← coheight_orderIso irreducibleSetEquivPoints Z]
  exact (congrArg _ ((U i).isOpenEmbedding'.coheight_eq (x := (⟨_, hi⟩ : U i)))).trans_le
    ((coheight_le_topologicalKrullDim _).trans (h i))
