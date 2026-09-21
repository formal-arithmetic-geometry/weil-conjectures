/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sets.Closeds
public import WeilConjectures.Mathlib.Topology.Irreducible

/-!
# Irreducible closed subsets of a closed subspace

A closed subspace of a topological space `α` has for irreducible closed subsets exactly the
irreducible closed subsets of `α` that it contains. This file records that bijection as an order
isomorphism, in the shape of the open counterpart
`TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding` already in Mathlib.

## Main definitions

* `TopologicalSpace.IrreducibleCloseds.orderIsoOfIsClosedEmbedding`: for a closed embedding
  `f : β → α`, the order isomorphism between `IrreducibleCloseds β` and the irreducible closed
  subsets of `α` contained in the range of `f`.
* `TopologicalSpace.IrreducibleCloseds.orderIsoIic`: its form for the inclusion of an
  irreducible closed subset `T` of `α`, namely `IrreducibleCloseds ↥T ≃o Iic T`.
-/

@[expose] public section

open Set Topology

namespace TopologicalSpace.IrreducibleCloseds

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- Along a closed embedding `f : β → α`, the irreducible closed subsets of `β` are order
isomorphic to the irreducible closed subsets of `α` contained in the range of `f`. -/
def orderIsoOfIsClosedEmbedding (f : β → α) (hf : IsClosedEmbedding f) :
    IrreducibleCloseds β ≃o {V : IrreducibleCloseds α | (V : Set α) ⊆ range f} where
  toFun V :=
    ⟨{ carrier := f '' V
       isIrreducible' := V.isIrreducible.image f hf.continuous.continuousOn
       isClosed' := hf.isClosedMap _ V.isClosed },
      image_subset_range f V⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := (hf.isEmbedding.isIrreducible_preimage_iff V.2).2 V.1.isIrreducible
      isClosed' := V.1.isClosed.preimage hf.continuous }
  left_inv _ := IrreducibleCloseds.ext (hf.injective.preimage_image _)
  right_inv V := Subtype.ext (IrreducibleCloseds.ext (image_preimage_eq_of_subset V.2))
  map_rel_iff' := image_subset_image_iff hf.injective

/-- The irreducible closed subsets of an irreducible closed subspace `T` of `α` are order
isomorphic to the irreducible closed subsets of `α` contained in `T`. Irreducibility of `T` is
used only to phrase the codomain as an interval of `IrreducibleCloseds α`. -/
def orderIsoIic (T : IrreducibleCloseds α) : IrreducibleCloseds (T : Set α) ≃o Iic T :=
  (orderIsoOfIsClosedEmbedding _ T.isClosed.isClosedEmbedding_subtypeVal).trans
    (OrderIso.setCongr _ _ (by ext V; simp [← SetLike.coe_subset_coe]))

end TopologicalSpace.IrreducibleCloseds
