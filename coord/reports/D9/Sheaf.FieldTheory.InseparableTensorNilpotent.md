## What changed

Proved `FieldTheory.inseparable_tensorProduct_algebraicClosure_not_isReduced` in
`Sheaf.FieldTheory.InseparableTensorNilpotent`, with its statement unchanged.
The proof embeds the minimal-polynomial quotient into K, preserves the injection by
flat base change, and identifies the base-changed quotient using `AdjoinRoot.tensorAlgEquiv`
and `AdjoinRoot.mapAlgEquiv`. Reducedness would make the mapped minimal polynomial radical,
squarefree and hence separable over the perfect field kbar, contradicting inseparability.
The definition of reducedness then gives the requested nonzero nilpotent.

Added proof-only imports of `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`,
`Mathlib.RingTheory.Flat.Basic`, and `Mathlib.RingTheory.Ideal.Quotient.Nilpotent`.
Updated the declaration's proof documentation and the node's proof and proof origin.
There are no definition, statement or visibility changes, and no consumer adaptations.

## Proved and sorry left

Closed the original hole in
`FieldTheory.inseparable_tensorProduct_algebraicClosure_not_isReduced`
(node `lem-pc-inseparable-tensor-nilpotent`): 1 of 1 proved, 0 holes added, 0 remaining.
No split-offs and no dependence on any project theorem containing sorry.

## No longer needed

No existing imports, dependency nodes or modules are pruned. The declared dependency
`lem-weil-pbc-minimal-polynomial-quotient-field-iso` is used through its Mathlib declaration
`IntermediateField.adjoinRootEquivAdjoin`.

The explicit repeated-root choice, degree comparison and calculation of a square-zero
polynomial class are unnecessary: the radical/squarefree criterion for the quotient gives
failure of reducedness directly. These were proof steps with no separate nodes or modules.
During development, redundant trial imports of `Mathlib.FieldTheory.Perfect`,
`Mathlib.FieldTheory.IsSepClosed`, and `Mathlib.RingTheory.Nilpotent.Lemmas` were removed;
the final imports already expose the needed declarations.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The planned repeated-root argument is mathematically valid but
requires more polynomial calculations than the equivalent radical/squarefree argument.
The node now records the actual Lean proof. Its unit record has no realized nodes to bypass,
and the original minimal-polynomial quotient dependency remains in use.

The cited Stacks 030V/030W discuss geometric reducedness and separability; the explicit
minimal-polynomial repeated-root calculation in the old docstring is an auxiliary argument,
not the literal proof printed at those source labels. The replacement is identified as an
agent-written argument in `proof_origin`.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
