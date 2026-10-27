## What changed

Proved `commonStageDerivedPullback_existsUnique` from two explicit intermediate
statements: the normalized pullback comparison family and the descent assembly
for a fixed coherent family. The tensor and internal-Hom declarations remain at
their original proof holes.

## Proved and sorry left

Closed 1 of the 3 original holes: `commonStageDerivedPullback_existsUnique`.
The following original holes remain: `commonStageDerivedTensor_existsUnique` and
`commonStageDerivedInternalHom_existsUnique`. Two strict intermediate statements
retain postponed proofs: `commonStagePullback_comparison_data` and
`commonStagePullback_descent_from_data`.

## No longer needed

None. No existing dependency or module was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan left both the coherent comparison family and the fixed
family descent assembly implicit. They are now explicit strict intermediate
statements, so the proved theorem only performs their genuine composition.

## New nodes

- `lem-weil-common-stage-pullback-comparison-data`
- `lem-weil-common-stage-pullback-descent-from-data`

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
