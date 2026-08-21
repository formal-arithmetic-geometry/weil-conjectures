/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Constructions

/-!

# Density of an overlap in the union

If a dense set is contained in two open sets `U` and `V`, then `U ∩ V` is dense in the
subspace `U ∪ V`. This is the induction invariant for the affine open cover in the
Noetherian case of Nagata's compactification theorem: the overlap of a partial union of the
cover with the next chart is dense in the enlarged partial union, because it contains the
dense total intersection of the cover (blueprint:
`lemma:nagata-partial-union-overlap-dense`).

-/

@[expose] public section

open Set

variable {α : Type*} [TopologicalSpace α]

/-- If a dense set is contained in both open sets `U` and `V`, then `U ∩ V` is dense in the
subspace `U ∪ V` (blueprint: `lemma:nagata-partial-union-overlap-dense`). -/
theorem Dense.preimage_val_inter {D U V : Set α} (hD : Dense D) (hUV : IsOpen (U ∪ V))
    (hU : D ⊆ U) (hV : D ⊆ V) : Dense ((↑) ⁻¹' (U ∩ V) : Set (U ∪ V : Set α)) :=
  (hD.mono (subset_inter hU hV)).preimage hUV.isOpenMap_subtype_val
