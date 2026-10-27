## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarCounitNormalization` in
`Sheaf.Paper.TowerScalarCounitNormalization`, preserving its entire signature.
The proof uses the existing `ScalarData.transpose_model` equation and the third
Chern normalization. The proved private helpers establish K-flatness of the
coefficient single using the tensor right unitor and compute the ordinary
adjunction on single complexes. These adapt the calculations already proved in
`TowerChernScalarUnit`; that module is not imported. Added the proof-only import
`Mathlib.Algebra.Homology.Monoidal`. Expanded the existing node's proof to record
the implemented calculation and cancellation. No other existing module changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.SpTowerClasses.scalarCounitNormalization`
(node `lem-sp-tower-scalar-counit-normalization`). No holes remain in the item;
no holes were added or split off. Both private helpers are completely proved.
Server single-file compilation passed cleanly in 38.0 seconds via `lcompile.py`.

## No longer needed

None. All three original proof dependencies remain used. No imports, nodes or
modules are withdrawn. In particular, no new dependency on
`TowerChernScalarUnit` or its scalar-constraint coherence obligation is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing proof of
`exists_normalizedScalarUnit` already contains the coefficient K-flatness and
single-complex adjunction calculations needed here. The current server queue
lists this item as `proof`, with no current build-error or rework record.
The blueprint unit route is unchanged; this completes its scalar normalization
step directly, without another split.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
