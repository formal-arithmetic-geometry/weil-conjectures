/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Constructions

/-!
# Density in an open subspace

- `Dense.preimage_val`: a dense subset of a space restricts to a dense subset of any
  open subspace;
- `Dense.preimage_val_inter`: if a dense set is contained in two sets `U` and `V` whose
  union is open, then `U ∩ V` is dense in the subspace `U ∪ V` (blueprint:
  `lemma:nagata-partial-union-overlap-dense`).
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A dense subset of a space restricts to a dense subset of any open subspace. -/
protected theorem Dense.preimage_val {D A : Set X} (hD : Dense D) (hA : IsOpen A) :
    Dense ((↑) ⁻¹' D : Set A) :=
  hD.preimage hA.isOpenMap_subtype_val

/-- **Dense overlap of a partial union**: if a dense subset of `X` is contained in two
sets `U` and `V` whose union is open, then `U ∩ V` is dense in the subspace `U ∪ V`.
This is the induction invariant used to glue compactifications along a finite affine
cover with dense total intersection.
(Blueprint: `lemma:nagata-partial-union-overlap-dense`.) -/
theorem Dense.preimage_val_inter {D U V : Set X} (hD : Dense D) (hUV : IsOpen (U ∪ V))
    (hDU : D ⊆ U) (hDV : D ⊆ V) :
    Dense ((↑) ⁻¹' (U ∩ V) : Set ↥(U ∪ V)) :=
  (hD.preimage_val hUV).mono (preimage_mono (subset_inter hDU hDV))
