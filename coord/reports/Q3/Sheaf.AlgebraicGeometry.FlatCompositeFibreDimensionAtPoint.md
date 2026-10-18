## What changed

Proved `AlgebraicGeometry.flat_composite_fibre_dimension_at_point` from the stated
composite-fibre local models, the finite-type dimension formula, and Mathlib's
flat height and transcendence-degree tower formulas. Four proved private helpers
handle the local-ring dimension calculation, transport from an open subscheme,
the canonical fibre scalar map, and the dimension formula for a fibre.

Converted the assigned legacy file to the module-system header required by the
brief. Its existing theorem signature is unchanged. Statement dependencies are
public imports; proof dependencies are ordinary imports. The interface change is recorded in
`coord/changes/flat-composite-fibre-dimension-module-interface.md`. No other module imports
this module in the shared source tree (`tools/downstream.py`, 2026-10-18).

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.flat_composite_fibre_dimension_at_point`
(node `lem-sbc-flat-composite-fibre-dimension-at-point`).
Added zero holes. No `sorry` remains in the delivered module.
The full module compiled cleanly through `lcompile.py` in 7.8 seconds. This is a proof
from the existing declared dependencies; `composite_fibre_local_models` remains
an existing obligation outside this delivery.

## No longer needed

Removed the import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
The proof does not need `lem-kun-dimension-finite-type` or its declaration
`AlgebraicGeometry.exists_topologicalKrullDim_le`: addition in `WithBot ENat`
works directly, with no subtraction, cancellation, or finiteness bound.
Removed that node from `proof_deps` and from the obsolete `tool_uses` list.
All five other declared proof dependencies remain in use. The unit route is
unchanged; no new nodes or public intermediate statements were introduced.

## Where the brief, the DAG or earlier work was wrong

The shared assigned file was still a legacy non-module file despite the note in
its node recording a previous header conversion. This delivery supplies the
required header. The proof plan's finiteness argument is unnecessary, as the last
step of the node already observes. No mathematical statement or definition was
changed.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
