## What changed

Added the Y-side representative-equation substep as a named theorem so the remaining
pullback/mate square can use it. Its proof is split off for a later worker; the assigned
pullback square remains open.

## Proved and sorry left

No holes were closed. The assigned theorem `finiteScalarTensorPullback_onRepresentatives`
remains as its original `sorry`; the split theorem
`finiteScalarTensorRealization_Y_representative` is a second `sorry` left for a later
worker.

## No longer needed

None. The assigned module still needs all of its original proof imports; the new helper
uses only the finite-scalar realization and tensor-complex modules.

## Where the brief, the DAG or earlier work was wrong

The original proof plan exposes a representative equation that can be discharged
independently, but the remaining pullback/mate square still requires the planned
normalization argument.

## New nodes

`lem-sf-finite-scalar-tensor-pullback-representative-equation` records the new Y-side
representative substep.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
