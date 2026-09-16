/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Irreducible

/-!
# Irreducible subsets of a subspace

A subset `V` of a subspace `S` of a topological space `X` can be seen either as a subset of `X`
contained in `S`, or as a subset of the space `↥S`. This file records that the two points of
view agree on irreducibility, and consequently that the irreducible components of the space
`↥S` are, seen in `X`, the maximal irreducible subsets of `S`.

## Main results

* `isIrreducible_preimage_val_iff`: for `V ⊆ S`, the subset `S ↓∩ V` of `↥S` is irreducible if
  and only if `V` is irreducible.
* `maximal_isIrreducible_image_val`: the image in `X` of an irreducible component of `↥S` is a
  maximal irreducible subset of `S`.
-/

@[expose] public section

open Set Set.Notation Topology

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- For a subset `V` of a subspace `S` of `X`, being irreducible in `↥S` and being irreducible
in `X` are the same thing. -/
theorem isIrreducible_preimage_val_iff (h : V ⊆ S) :
    IsIrreducible (S ↓∩ V) ↔ IsIrreducible V := by
  rw [isIrreducible_iff_irreducibleSpace, isIrreducible_iff_irreducibleSpace]
  exact Homeomorph.irreducibleSpace_iff
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by rwa [Subtype.range_coe]))

/-- The image in `X` of an irreducible component of a subspace `S` is a maximal irreducible
subset of `S`. -/
theorem maximal_isIrreducible_image_val {T : Set S} (hT : T ∈ irreducibleComponents S) :
    Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) ((↑) '' T) := by
  refine ⟨⟨hT.1.image _ continuous_subtype_val.continuousOn, Subtype.coe_image_subset S T⟩, ?_⟩
  rintro W ⟨hWirr, hWS⟩ hTW
  have hW : IsIrreducible (S ↓∩ W) := (isIrreducible_preimage_val_iff hWS).2 hWirr
  have hTW' : T ⊆ S ↓∩ W := fun x hx ↦ hTW ⟨x, hx, rfl⟩
  calc W = (↑) '' (S ↓∩ W) := by
        rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hWS]
    _ ⊆ (↑) '' T := Set.image_mono (hT.2 hW hTW')
