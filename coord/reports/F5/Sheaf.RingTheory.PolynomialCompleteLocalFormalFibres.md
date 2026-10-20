## What changed

Retired the duplicate `Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres` module.
The same theorem statement is already proved in the adopted source module
`WeilConjectures.RingTheory.PolynomialCompleteLocalFormalFibres` as
`Polynomial.isRegular_algebraMap_adicCompletion_localization`, with only the declaration
name changed. The item node now points to that canonical declaration. The retired module
had zero `sorry`s; this delivery removes the duplicate module as required by the queue's
`retire` assignment. The interface change is recorded in
`coord/changes/retire-polynomial-complete-local-formal-fibres.md`.

## Proved and sorry left

No holes were present or added. The canonical upstream theorem has no `sorry` and uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The deleted duplicate module and its proof imports are no longer needed. No current module
imports the deleted `Sheaf` path. The source module and its existing upstream imports remain
in use by `WeilConjectures.RingTheory.PolynomialGRingComparison`.

## Where the brief, the DAG or earlier work was wrong

The queue classified this module for retirement, while the old node attachment still named
the retired Sheaf duplicate. The adopted source tree contains the identical theorem under
`isRegular_algebraMap_adicCompletion_localization`; the node attachment has been corrected.

## New nodes

None.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
