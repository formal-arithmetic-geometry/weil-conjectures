/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sets.Closeds
public import WeilConjectures.Mathlib.Topology.Irreducible

/-!
# Irreducible closed subsets of an irreducible closed subspace

An irreducible closed subset `T` of a topological space `α` is itself a topological space, and
its irreducible closed subsets are exactly the irreducible closed subsets of `α` contained in
`T`. This file records that bijection as an order isomorphism.

## Main results

* `TopologicalSpace.IrreducibleCloseds.orderIsoIic`: the order isomorphism
  `IrreducibleCloseds ↥T ≃o Set.Iic T`, for `T` an irreducible closed subset of `α`.
-/

@[expose] public section

open Set Set.Notation

namespace TopologicalSpace.IrreducibleCloseds

variable {α : Type*} [TopologicalSpace α]

/-- The irreducible closed subsets of an irreducible closed subspace `T` of `α` are order
isomorphic to the irreducible closed subsets of `α` contained in `T`. -/
def orderIsoIic (T : IrreducibleCloseds α) : IrreducibleCloseds (T : Set α) ≃o Set.Iic T where
  toFun V :=
    ⟨⟨Subtype.val '' (V : Set (T : Set α)),
      V.isIrreducible.image _ continuous_subtype_val.continuousOn,
      by exact T.isClosed.isClosedMap_subtype_val _ V.isClosed⟩,
      by exact Subtype.coe_image_subset _ _⟩
  invFun W :=
    ⟨(T : Set α) ↓∩ (W : Set α),
      (isIrreducible_preimage_val_iff
        (SetLike.coe_subset_coe.2 (Set.mem_Iic.1 W.2))).2 W.1.isIrreducible,
      W.1.isClosed.preimage continuous_subtype_val⟩
  left_inv V := IrreducibleCloseds.ext (preimage_image_eq _ Subtype.val_injective)
  right_inv W := Subtype.ext <| IrreducibleCloseds.ext <|
    (Subtype.image_preimage_coe _ _).trans
      (inter_eq_right.2 (SetLike.coe_subset_coe.2 (Set.mem_Iic.1 W.2)))
  map_rel_iff' {V V'} := by exact image_subset_image_iff Subtype.val_injective

end TopologicalSpace.IrreducibleCloseds
