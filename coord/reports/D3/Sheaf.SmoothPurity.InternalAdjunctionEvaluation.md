## What changed
Proved `internalAdjunctionEvaluation` by reducing it to the canonical parametrized-adjunction mate calculation. Added a named intermediate theorem for the mate core.

## Proved and sorry left
`AlgebraicGeometry.Etale.internalAdjunctionEvaluation` is proved. `internalAdjunctionEvaluation_mate_core` remains as one named sorry, split off because it is the strict tensor-Hom mate identity used by the target.

## No longer needed
The K-injective and global-sections imports from the original plan are not used by the reduced mate proof.

## Where the brief, the DAG or earlier work was wrong
The full resolution-level plan is unnecessary: the named internal-adjunction is definitionally the parametrized conjugate of the projection map.

## New nodes
`lem-asd-internal-adjunction-evaluation-mate-core` records the strictly lower-level mate identity.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
