/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Passing to a proper closed subset raises the dimension by at least one

## Main results

* `topologicalKrullDim_add_one_le`: if `X` is an irreducible topological space and `Z` is a
  proper irreducible closed subset of `X`, then `dim Z + 1 ≤ dim X`. Indeed a chain of
  irreducible closed subsets of `Z` is a chain of irreducible closed subsets of `X`, all of them
  contained in `Z` and hence strictly smaller than `X` itself, so appending `X` to it gives a
  chain of length one more.
-/

@[expose] public section

open Order Set TopologicalSpace

/-- If `Z` is a proper irreducible closed subset of an irreducible topological space `X`, then
the Krull dimension of `Z` is at least one less than the Krull dimension of `X`. -/
theorem topologicalKrullDim_add_one_le {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    {Z : Set X} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hZ : Z ≠ Set.univ) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  have hZne : Nonempty Z := hZi.nonempty.to_subtype
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨closure {Classical.arbitrary Z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  rw [topologicalKrullDim, topologicalKrullDim, krullDim_eq_iSup_length,
    krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add, ENat.iSup_add,
    WithBot.coe_le_coe, iSup_le_iff]
  intro l
  let top : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have key : ∀ W : IrreducibleCloseds Z,
      IrreducibleCloseds.map (Subtype.val) continuous_subtype_val W < top := by
    intro W
    have hsub : (IrreducibleCloseds.map (Subtype.val) continuous_subtype_val W : Set X) ⊆ Z := by
      rw [IrreducibleCloseds.coe_map]
      exact closure_minimal (by rintro _ ⟨⟨x, hx⟩, -, rfl⟩; exact hx) hZc
    refine lt_of_le_of_ne (Set.subset_univ _) fun h ↦ hZ (Set.eq_univ_of_univ_subset ?_)
    exact fun x hx ↦ hsub (h ▸ hx)
  refine le_trans ?_ (le_iSup _
    ((l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing
      Topology.IsInducing.subtypeVal)).snoc top (key _)))
  simp
