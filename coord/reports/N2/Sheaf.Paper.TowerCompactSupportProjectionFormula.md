## What changed

Completed the preserved proof of `maps_natural` and verified the preserved proof of
`canonicalIso_natural`. The module remains proof-only: no statements, definitions,
nodes, or public imports were changed.

## Proved and sorry left

Closed:

- `AlgebraicGeometry.ProEtale.SpTowerProjection.maps_natural`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.canonicalIso_natural`.

Three original holes remain:

- `AlgebraicGeometry.ProEtale.SpTowerProjection.properMap_evaluation`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.openMap_evaluation`.
- `AlgebraicGeometry.ProEtale.SpTowerProjection.tower_compact_support_projection_formula`.

No new sorries or split nodes were added. The item file compiles, and the latest
delivery dry run passed preflight.

## No longer needed

No imports or DAG dependencies were removed. The proof uses the existing naturality
and projection interfaces; no additional modules are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly described `canonicalIso_natural` as unverified. Its
proof is now included in the item file and the complete file compile succeeds.

A direct attempt to prove `properMap_evaluation` by unfolding the generic
`ProjectionEvaluation` equation with `simpa` exceeded the single-file compile
limit. That experiment was reverted. A separate scratchpad transport attempt also
exceeded the remote compile limit; neither changed the delivered item.

The retained delivery dry run completed successfully with commit
`5226dc2a24`, review class AUTO. The session was restarted during provider
failures, resetting the reference clock; no budget files were edited.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
