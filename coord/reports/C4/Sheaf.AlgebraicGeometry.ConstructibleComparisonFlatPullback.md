## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ConstructibleComparisonFlatPullback.lean` from its
quarantined source. The module proves both declarations recorded by the node:
`AlgebraicGeometry.ProEtale.constructibleComparisonPullback_flat` and
`AlgebraicGeometry.ProEtale.constructibleComparisonComplexPullback_kFlat`.
The proof uses the continuous ringed-topos direct-image construction, supplied K-flat
pullback theorem, bounded-above flat-complex theorem, and uniqueness of left adjoints.
No public signatures or node statements were changed.

## Proved and sorry left

Closed the two existing holes:

- `AlgebraicGeometry.ProEtale.constructibleComparisonPullback_flat`
- `AlgebraicGeometry.ProEtale.constructibleComparisonComplexPullback_kFlat`

No `sorry` remains in the delivered module, and no new `sorry` was added.

## No longer needed

None. The restored proof uses all five declared proof dependencies in the node and all
listed imports in the module.

## Where the brief, the DAG or earlier work was wrong

The module had been removed from the live tree by a cluster restore even though its
reviewed proof and node remained valid. The quarantined source compiles unchanged against
the current library; no mathematical or DAG correction was needed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
