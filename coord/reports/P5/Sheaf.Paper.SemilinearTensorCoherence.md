## What changed

The item theorem now assembles three explicitly named component interfaces into
`SystemTensorCoherence` with a real constructor. Added `SemilinearTensorBase`,
`SemilinearTensorComparisons`, and `SemilinearTensorReduction`; each isolates a
strictly smaller part of the tensor-coherence construction and is imported only by
the parent proof.

## Proved and sorry left

Closed the original `systemTensorCoherence_nonempty` hole: its proof is a complete
assembly from the three component declarations. Added three named split theorems,
all with documented sources and DAG nodes: `systemTensorBase_nonempty`,
`systemTensorComparisons_nonempty`, and `systemTensorReduction`. No `sorry` occurs
inside a definition.

## No longer needed

No proof-dependency imports were removed from the parent. The parent uses the
component modules and the scalar-coherence declaration; no additional planned node
was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node bundled base tensor descent, evaluation/scalar comparison, and
reduction compatibility into one existence proposition, while the available Lean
APIs expose these as separate construction boundaries. The delivery records those
boundaries as three strictly smaller intermediate statements so the parent assembly
is checkable.

## New nodes

`lem-coef-semilinear-tensor-base` records the base closed structures and models;
`lem-coef-semilinear-tensor-comparisons` records normalized evaluation and scalar
comparisons; `lem-coef-semilinear-tensor-reduction` records the reduction equation.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
