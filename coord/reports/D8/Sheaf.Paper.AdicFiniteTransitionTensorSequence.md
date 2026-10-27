## What changed

The assigned theorem `AlgebraicGeometry.Scheme.adicFiniteTransition_tensor_sequence` now
constructs its residue complex `P` using the existing
`exists_coefficientModelFlatKFlatRepresentative` theorem and then invokes a new,
strictly smaller conditional theorem
`adicFiniteTransition_tensor_sequence_core`. The latter is in
`Sheaf.Paper.AdicFiniteTransitionTensorSequenceCore` and isolates the remaining
coefficient-kernel construction for a fixed `P` and comparison. The parent node's
proof and dependency fields were updated to match this route.

## Proved and sorry left

Closed the original sorry in
`AlgebraicGeometry.Scheme.adicFiniteTransition_tensor_sequence` by a real proof of the
residue-model existential step and composition with the core statement.

Added one strictly smaller named theorem with a sorry:
`AlgebraicGeometry.Scheme.adicFiniteTransition_tensor_sequence_core` in node
`lem-sfb-adic-finite-transition-tensor-sequence-core`. It omits the outer existential
choice of `P` and assumes the K-flat and residue-comparison data as hypotheses.

## No longer needed

No imports were removed. The proof uses `Sheaf.AlgebraicGeometry.CoefficientTorFlatModel`
and the new core module; no additional planned dependency was introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier split correctly isolated the coefficient-kernel construction, but the outer
residue-model witness was still left inside the same sorry. The existing flat K-flat
representative theorem proves that witness directly, so it is now discharged before the
remaining conditional construction. No target statement or definition was changed.

## New nodes

`lem-sfb-adic-finite-transition-tensor-sequence-core` records the remaining transition
sequence after fixing a K-flat residue model and its comparison. Its module is
`lean/Sheaf/Paper/AdicFiniteTransitionTensorSequenceCore.lean`.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
