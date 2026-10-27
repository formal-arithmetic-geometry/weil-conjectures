## What changed

Proved `AlgebraicGeometry.Scheme.normalizedTower_common_lisse_strata` by applying the existing
`NormalizedTowerCoefficients.native_common_strata` construction at the first quotient and
then the new propagation interface. Added the proof-only import
`Sheaf.Paper.NormalizedTowerLissePropagation`. Replaced the private duplicate native-sieve
predicate by an abbreviation to the public predicate used by the split theorem, preserving
its meaning and all existing helper proofs.

## Proved and sorry left

Closed the `sorry` in `normalizedTower_common_lisse_strata`.
The delivery adds one strictly simpler intermediate theorem, whose proof remains `sorry`:
`AlgebraicGeometry.Scheme.normalizedTower_lisse_of_native_strata`, node
`new-lem-weil-pbc-normalized-tower-lisse-propagation`. It isolates propagation from fixed
level-zero native finite models to all normalized levels.

## No longer needed

No imports or declared proof dependencies were removed. The original direct hard propagation
steps are represented by the named intermediate node above.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the level-zero common-strata construction and nilpotent
propagation into one theorem without a Lean declaration for the propagation step. The route
was therefore split at that genuine intermediate conclusion; no target statement was changed.

## New nodes

`new-lem-weil-pbc-normalized-tower-lisse-propagation` in
`dag/nodes/sec-proper-base-change/new-lem-weil-pbc-normalized-tower-lisse-propagation.json`
records the intermediate theorem and its Stacks Tag 094I nilpotent-propagation source.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
