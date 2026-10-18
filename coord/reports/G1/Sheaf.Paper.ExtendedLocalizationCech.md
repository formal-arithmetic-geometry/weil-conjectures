## What changed

Filled `insert_degree`, `mapSection_naturality`, and `unitMap_existsUnique` with compiling proofs.
The remaining construction theorems retain their original named `sorry` proofs.

## Proved and sorry left

Proved: `insert_degree`, `mapSection_naturality`, `unitMap_existsUnique`.
Sorry left: `differential_sq`, `transition_comm`, `comparison_comm`,
`comparisonCocone_naturality`, `idealRow_comparison_zero`, `augmentation_incoming`,
`augmentation_naturality`.

## No longer needed

No imports or DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The module's explicit Koszul cancellation and transition proofs require substantial
coproduct and sheaf-module extensionality not supplied by the current declarations;
no statement was changed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
