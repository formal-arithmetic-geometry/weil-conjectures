/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension as the supremum of local dimensions

## References

* Stacks Project, Tag 0B7I.
-/

@[expose] public section

universe u

/-- For every topological space, its Krull dimension is the supremum of its local dimensions. -/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt
    (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  classical
  apply le_antisymm
  · change Order.krullDim (TopologicalSpace.IrreducibleCloseds X) ≤ _
    unfold Order.krullDim
    refine iSup_le fun p ↦ ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    refine le_trans ?_ (le_iSup (fun x : X ↦ topologicalKrullDimAt x) x)
    unfold topologicalKrullDimAt
    refine le_iInf₂ fun U hxU ↦ ?_
    let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (Subtype.val : U → X) U.isOpenEmbedding'
    let q : LTSeries
        {Z : TopologicalSpace.IrreducibleCloseds X |
          (Subtype.val ⁻¹' (Z : Set X) : Set U).Nonempty} :=
      LTSeries.mk p.length
        (fun i ↦ ⟨p i, ⟨⟨x, hxU⟩, p.head_le i hx⟩⟩)
        (fun i j hij ↦ p.strictMono hij)
    exact Order.LTSeries.length_le_krullDim (q.map e.symm e.symm.strictMono)
  · refine iSup_le fun x ↦ ?_
    exact (iInf₂_le ⊤ trivial).trans
      (topologicalKrullDim_subspace_le X Set.univ)
