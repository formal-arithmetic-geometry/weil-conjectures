/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Topology.SpectralSpace.WLocal.ConnectedComponents

/-!
# Connected components of w-local spaces as generalization sets

In a w-local space, the connected component of a closed point `c` is the set of
generalizations of `c`.

## Main results

* `WLocalSpace.connectedComponent_eq_setOf_specializes`: in a w-local space,
  `connectedComponent c = {x | x ⤳ c}` for every closed point `c`.
-/

@[expose] public section

/-- In a w-local space, the connected component of a closed point `c` consists exactly of the
generalizations of `c`. This is the topological content of blueprint
`proposition-w-local-components--2`. -/
lemma WLocalSpace.connectedComponent_eq_setOf_specializes {X : Type*} [TopologicalSpace X]
    [WLocalSpace X] {c : X} (hc : c ∈ closedPoints X) :
    connectedComponent c = {x | x ⤳ c} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hxc ↦
    ConnectedComponents.coe_eq_coe'.mp hxc.connectedComponents_mk_eq⟩
  obtain ⟨p, hp, hxp⟩ := exists_isClosed_specializes x
  have hpc : p = c := WLocalSpace.closedPoints_eq_of_mk_eq (mem_closedPoints_iff.mpr hp) hc
    (hxp.connectedComponents_mk_eq.symm.trans (ConnectedComponents.coe_eq_coe'.mpr hx))
  exact hpc ▸ hxp
