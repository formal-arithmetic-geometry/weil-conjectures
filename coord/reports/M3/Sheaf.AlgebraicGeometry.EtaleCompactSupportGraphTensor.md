## What changed

Added the adjunction-transpose calculation in `EtaleCompactSupportGraphTensor` and a
split-off core mate theorem in `EtaleCompactSupportGraphTensorCore`. The main theorem is
proved by the generic projection transpose identity and the core mate equation; the
compactification projection formula is normalized by
`projectionMapOfCompactification_app_app`.

## Proved and sorry left

`compactSupportGraph_tensor_evaluation` is proved. The split-off theorem
`compactSupportGraph_tensor_evaluation_core` remains `sorry` and is recorded by node
`lem-pur-compact-support-graph-tensor-evaluation-core`.

## No longer needed

No imports or declared proof dependencies were removed. The original multi-step K-flat and
localization route is encapsulated by the core mate node; the main theorem only needs the
core node and the categorical transpose calculation.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted the explicit categorical transpose lemma needed to
connect the compactification projection map to the displayed graph composite. This delivery
adds that elementary lemma and records the remaining geometric/K-flat calculation as a
strictly simpler core mate statement.

## New nodes

`lem-pur-compact-support-graph-tensor-evaluation-core` is the core compactification mate
equation. Its declaration is in
`lean/Sheaf/AlgebraicGeometry/EtaleCompactSupportGraphTensorCore.lean`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
