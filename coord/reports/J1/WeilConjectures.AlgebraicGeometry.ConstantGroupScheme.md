## What changed

Filled `AlgebraicGeometry.exists_constantGroupSchemeMultiplication` in
`lean/WeilConjectures/AlgebraicGeometry/ConstantGroupScheme.lean`. The proof constructs the
pairwise pullback cover, proves its distinct components are disjoint, glues the local
component maps with `Scheme.Cover.glueMorphisms`, and proves the prescribed restriction and
codiagonal equations. Added the proof-only import `Mathlib.AlgebraicGeometry.PullbackCarrier`.

## Proved and sorry left

Proved and closed the only sorry, `AlgebraicGeometry.exists_constantGroupSchemeMultiplication`.
No sorries remain in the delivered module and no new sorries were added.

## No longer needed

None. No existing imports were removed and no DAG nodes or modules were pruned. The existing
coproduct, fibre-product, open-immersion and gluing dependencies remain needed; the proof uses
their Mathlib APIs directly. No additional Sheaf module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing proof of
`AlgebraicGeometry.constantGroupSchemeMultiplication_properties` in
`Sheaf.AlgebraicGeometry.ConstantGroupSchemeMultiplication` already implements the gluing route,
but that module imports this item and cannot be imported back without a cycle. Its disjointness
and gluing argument was used here with the additional restriction-formula calculation. No
statement, definition or unit route was changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
