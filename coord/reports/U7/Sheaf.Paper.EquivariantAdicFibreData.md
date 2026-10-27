## What changed

Completed `AlgebraicGeometry.ProEtale.EquivariantAdicFibre.fibre_isTopologicalAddGroup`
in `Sheaf.Paper.EquivariantAdicFibreData`. Equip each object of the tower locally with
its specified discrete topology. Mathlib gives a topological additive group on the
product, and `topologicalAddGroup_induced` transports it along the compatible-sections
submodule inclusion. The resulting induced topology is definitionally `fibreTopology`.
No declarations, definitions, signatures, or imports changed outside this proof.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.EquivariantAdicFibre.fibre_isTopologicalAddGroup`
(node `def-sfb-equivariant-adic-fibre-data`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module.

## No longer needed

None. No imports, nodes, or modules were removed. The definition node has no
planned proof dependencies; the direct Mathlib argument proves its existing
additive-topology obligation without adding any dependency or changing the unit route.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring already describes the direct product-and-subspace proof.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
