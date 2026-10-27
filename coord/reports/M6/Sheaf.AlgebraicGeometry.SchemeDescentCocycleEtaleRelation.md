## What changed

Filled `AlgebraicGeometry.SchemeDescentCocycle.etale_relation` in the assigned module.
The existing statement, six abbreviations and imports are preserved. Added only proved
private helpers for overlap coordinates, componentwise endpoint uniqueness, étaleness
and the equality over the base. The main proof constructs the diagonal and reversal
maps by coproduct descent and glues local composite arrows on a common pullback open cover.
The node now describes these concrete constructions.
The full proof compiled on the project server in 6.6 seconds; the unused covering
hypothesis is explicitly referenced without changing its binder. Delivery runs the
final compile and mechanical preflight checks.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.SchemeDescentCocycle.etale_relation`
(node `lem-trf-scheme-descent-cocycle-etale-relation`). No holes added, none split off,
and no `sorry` remains in the delivery.

## No longer needed

None. All seven declared proof dependencies are used through their existing Mathlib
APIs; no dependency module, node or import is pruned. Reflexivity and symmetry use
coproduct descent directly rather than gluing after pulling back to each test scheme.
The common open refinement in transitivity needs no connectedness assumption.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Joint surjectivity of the covering family is
not needed to construct the relation; it is retained verbatim in the theorem signature.
The empty index type and empty pieces are handled by the initiality of empty schemes.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
