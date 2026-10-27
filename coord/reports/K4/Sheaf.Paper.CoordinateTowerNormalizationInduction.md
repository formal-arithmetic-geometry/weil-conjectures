## What changed

Closed the three direct construction equalities in `lean/Sheaf/Paper/CoordinateTowerNormalizationInduction.lean`:
`zero_successor`, `thetaStepRaw_target`, and `projectionGammaRaw_target`.
The first uses the affine-space composition formula and `map_zero`; the latter two unfold
the recorded raw constructions (with zero/successor cases for the projection). Public imports,
signatures, definitions, and the DAG node are unchanged.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.zero_successor`
- `AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.thetaStepRaw_target`
- `AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.projectionGammaRaw_target`

Two original holes remain:
`AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.target_properties` and
`AlgebraicGeometry.ProEtale.CoordinateTowerNormalization.coordinateTower_normalization_induction`.
No holes were added and no statements were split off.

## No longer needed

No imports, nodes, or modules were removed. The attempted ordered-integration route for
`target_properties` was discarded because this module exceeded the fixed compile limit; it
introduced no delivered dependency or source change.

## Where the brief, the DAG or earlier work was wrong

No statement or DAG error was found. The remaining target-properties and induction proofs
are unchanged for a subsequent round.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
