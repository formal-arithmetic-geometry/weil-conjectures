## What changed

Proved `WeilConjectures.pointRestrictionPrimeUnits` in
`Sheaf.Paper.PointScalarCompatibleTransportTransfer` without changing its statement or any
construction. The proof obtains characteristic p from the recorded positive prime-power
cardinality of the finite base field. The distinct coefficient prime is therefore a unit;
its images in K, global sections of Spec K, and every stalk remain units.

Validation: the item compiled cleanly through lcompile.py (39.1 seconds, exit code 0).
The proof follows the existing docstring and keeps every public import and definition.

## Proved and sorry left

Closed 1 of the original 2 holes:
`WeilConjectures.pointRestrictionPrimeUnits`.

One original hole remains unchanged:
`WeilConjectures.PointScalarTransfer.scalar_compatible_transport_transfer`
(node `lem-weil-point-scalar-compatible-transport-transfer`).
No holes added, no statements split off, and no definition contains a new hole.
This is a partial delivery for the two-hole module, not a proof of the transfer theorem.

The transfer proof was explored using the recorded naturality, unit and tower clauses of
`pointSectionsScalarExtension`. Experimental calculations were not retained in the delivered
module. The outstanding theorem still has its full seven-step proof in its docstring and node,
including the raw additive realizations and fraction-valued comparison isomorphisms.

## No longer needed

None. No imports, nodes, modules or public declarations were removed. The unchanged transfer
statement and proof plan retain all their dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The rework row records an earlier quarantined import issue;
the current shared source exists and compiles. No archive or attachment was removed.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
