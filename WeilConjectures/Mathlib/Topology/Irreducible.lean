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
`↥S` are, seen in `X`, exactly the maximal irreducible subsets of `S`.

## Main results

* `Topology.IsEmbedding.isIrreducible_preimage_iff`: along an embedding `f`, a subset of the
  range of `f` is irreducible if and only if its preimage is.
* `isIrreducible_preimage_val_iff`: for `V ⊆ S`, the subset `S ↓∩ V` of `↥S` is irreducible if
  and only if `V` is irreducible.
* `maximal_isIrreducible_iff_preimage_val_mem_irreducibleComponents`: a subset of `S` is a
  maximal irreducible subset of `S` if and only if it is an irreducible component of `↥S`.
* `eq_univ_of_maximal_isIrreducible`: in an irreducible space the only maximal irreducible
  subset of `univ` is `univ` itself.
-/

@[expose] public section

open Set Set.Notation Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S V : Set X}

/-- A subset of the range of an embedding `f` is irreducible if and only if its preimage under
`f` is: the preimage is homeomorphic to the subset. -/
theorem Topology.IsEmbedding.isIrreducible_preimage_iff {f : Y → X} (hf : IsEmbedding f)
    (h : V ⊆ range f) : IsIrreducible (f ⁻¹' V) ↔ IsIrreducible V := by
  rw [isIrreducible_iff_irreducibleSpace, isIrreducible_iff_irreducibleSpace]
  exact Homeomorph.irreducibleSpace_iff
    ((hf.homeomorphImage _).trans (Homeomorph.setCongr (image_preimage_eq_of_subset h)))

/-- For a subset `V` of a subspace `S` of `X`, being irreducible in `↥S` and being irreducible
in `X` are the same thing. -/
theorem isIrreducible_preimage_val_iff (h : V ⊆ S) :
    IsIrreducible (S ↓∩ V) ↔ IsIrreducible V :=
  IsEmbedding.subtypeVal.isIrreducible_preimage_iff (by rwa [Subtype.range_coe])

/-- The image in `X` of an irreducible component of a subspace `S` is a maximal irreducible
subset of `S`. -/
theorem maximal_isIrreducible_image_val_of_mem_irreducibleComponents {T : Set S}
    (hT : T ∈ irreducibleComponents S) :
    Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) ((↑) '' T) := by
  refine ⟨⟨hT.1.image _ continuous_subtype_val.continuousOn, Subtype.coe_image_subset S T⟩, ?_⟩
  rintro W ⟨hWirr, hWS⟩ hTW
  have hW : IsIrreducible (S ↓∩ W) := (isIrreducible_preimage_val_iff hWS).2 hWirr
  calc
    W = (↑) '' (S ↓∩ W) := by rw [Subtype.image_preimage_coe, inter_eq_right.2 hWS]
    _ ⊆ (↑) '' T := image_mono (hT.2 hW (image_subset_iff.1 hTW))

/-- A maximal irreducible subset of a subspace `S` of `X` is, seen in `↥S`, an irreducible
component of `↥S`. -/
theorem preimage_val_mem_irreducibleComponents
    (hV : Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) V) : S ↓∩ V ∈ irreducibleComponents S := by
  refine ⟨(isIrreducible_preimage_val_iff hV.1.2).2 hV.1.1, fun U hU hVU ↦ ?_⟩
  have hsub : ((↑) '' U : Set X) ⊆ V := by
    refine hV.2 ⟨hU.image _ continuous_subtype_val.continuousOn, Subtype.coe_image_subset S U⟩ ?_
    calc
      V = (↑) '' (S ↓∩ V) := by rw [Subtype.image_preimage_coe, inter_eq_right.2 hV.1.2]
      _ ⊆ (↑) '' U := image_mono hVU
  exact image_subset_iff.1 hsub

/-- **The maximal irreducible subsets of a subspace `S` are its irreducible components**, seen
in the ambient space. -/
theorem maximal_isIrreducible_iff_preimage_val_mem_irreducibleComponents (h : V ⊆ S) :
    Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) V ↔ S ↓∩ V ∈ irreducibleComponents S := by
  refine ⟨preimage_val_mem_irreducibleComponents, fun hV ↦ ?_⟩
  have hmax := maximal_isIrreducible_image_val_of_mem_irreducibleComponents hV
  rwa [Subtype.image_preimage_coe, inter_eq_right.2 h] at hmax

/-- In an irreducible space the only maximal irreducible subset of `univ` is `univ` itself. -/
theorem eq_univ_of_maximal_isIrreducible [IrreducibleSpace X] {T : Set X}
    (hT : Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ (univ : Set X)) T) : T = univ :=
  univ_subset_iff.1 (hT.2 ⟨IrreducibleSpace.isIrreducible_univ X, Subset.rfl⟩ (subset_univ T))
