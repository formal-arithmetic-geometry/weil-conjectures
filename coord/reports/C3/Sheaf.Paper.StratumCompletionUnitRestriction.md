## What changed

Added the named intermediate theorem `AlgebraicGeometry.Scheme.stratumReduction_evaluation_on_KFlat` to isolate the K-flat representative calculation required by the remaining evaluation clause. The theorem is in the assigned module with its source and proof plan documented. The original public signatures and imports remain unchanged.

## Proved and sorry left

Closed 0 of the original 1 remaining holes. Added 1 split-off sorry: `AlgebraicGeometry.Scheme.stratumReduction_evaluation_on_KFlat`. The original `AlgebraicGeometry.Scheme.stratumReduction_evaluation` remains a sorry and is unchanged. The module compiles successfully.

## No longer needed

None. No imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The remaining proof requires a K-flat representative calculation followed by derived localization; the representative calculation is now an explicit strictly simpler node for parallel completion.

## New nodes

`lem-weil-pbc-stratum-completion-unit-restriction-evaluation-kflat` records the K-flat representative specialization of the remaining evaluation theorem.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
