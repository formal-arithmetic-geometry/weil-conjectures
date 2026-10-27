## What changed

Completed `AlgebraicGeometry.geometric_fibre_affine_chart_test` in the item module.
The comparison map is the universal lift into the original fibre. Pullback pasting and
cancellation prove that its square over `Spec H` is cartesian. Pasting again on each given
chart produces the tensor-spectrum comparison with both required projection formulas.
The pullback point-surjectivity theorem gives the covering condition; Mathlib's open-cover
and affine reducedness criteria finish the equivalence. The theorem statement stays unchanged. Removed unused imports of
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and
`Mathlib.RingTheory.TensorProduct.Maps`. Only the item's Lean module, its own DAG node,
and the import change record are changed. The proof docstring follows the actual route.
The change record is `coord/changes/geometric-fibre-affine-chart-test-imports.md`.
A direct-import search and `tools/downstream.py` both find zero current Lean importers;
no downstream adaptation is needed.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.geometric_fibre_affine_chart_test`
(node `lem-trf-geometric-fibre-affine-chart-test`). No holes added or split off.
No `sorry` remains in the delivered module. This is a complete proof from existing
Mathlib declarations, rather than a decomposition into new unproved statements.

## No longer needed

The node `lem-weil-pbc-fibre-of-base-change` is not needed by this proof: direct
construction of the map into the fibre and pullback pasting/cancellation produce the
arbitrary-`H` comparison without first passing through the fibre over `κ(t')`.
This is pruning of this item's dependency only, not withdrawal of that node elsewhere.
Removed the unused proof import `Mathlib.RingTheory.TensorProduct.Maps`; the standard
tensor constructions used here are already provided by the statement imports.
The unused public import
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions` is also removed. There are no
current Lean importers to adapt. No modules are withdrawn. The unit statement and its proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The DAG's intermediate residue-field
fibre is unnecessary for assembling this comparison. The proof makes the cover on
underlying scheme points explicit using `Scheme.Pullback.exists_preimage_pullback`;
this also handles the empty-cover and empty-chart cases without additional hypotheses.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
