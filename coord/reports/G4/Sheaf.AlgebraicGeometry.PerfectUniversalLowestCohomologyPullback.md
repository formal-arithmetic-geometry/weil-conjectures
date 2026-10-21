## What changed

Restored the quarantined module
`Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback` and
completed its theorem. The proof constructs the local zero-bottom models from
universal freeness,
uses `localZeroBottomModel_pullback`, and composes with the homology image of the derived pullback
composition isomorphism. The restored imports were adapted to export the source `DerivedPullback`
and `TensorPullback` interfaces needed by the public theorem signature. The import
change is recorded in `coord/changes/G4-PerfectUniversalLowestCohomologyPullback-imports.md`.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.perfectUniversalLowestCohomology_pullback`.
No `sorry` remains in the item, no holes were added, and no definitions contain `sorry`.

## No longer needed

No proof dependency or node is pruned. The proof uses all three declared proof dependencies:
`lem-sc-perfect-universal-lowest-zero-model`, `lem-sc-local-zero-bottom-model-pullback`, and
`lem-pc-ringed-spaces-derived-pullback-composition`.

## Where the brief, the DAG or earlier work was wrong

The module had been quarantined after a merge-queue restore. Its original proof remains valid, but
its private `Sheaf.AlgebraicGeometry.DerivedPullback` import did not expose `derivedPullback` and
`Modules.tensorPullback` for this restored public interface. Replacing that import with the upstream
public `WeilConjectures.AlgebraicGeometry.DerivedPullback` and adding its public `TensorPullback`
interface made the unchanged theorem compile. The theorem statement and proof route are unchanged.

## New nodes

None.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
