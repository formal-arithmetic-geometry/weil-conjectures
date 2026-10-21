## What changed

Restored `lean/Sheaf/CategoryTheory/CartanEilenbergDecalageInjectiveModel.lean` from its
quarantine path and retained its complete proof of
`CategoryTheory.cartanEilenberg_decalage_injective_model`. The proof uses the four
listed Cartan--Eilenberg helper modules already recorded by the DAG; no other files
or public interfaces changed.

## Proved and sorry left

The declaration `CategoryTheory.cartanEilenberg_decalage_injective_model` is proved.
This delivery leaves zero `sorry` declarations and adds no new holes.

## No longer needed

None. All four proof-dependency imports are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The prior quarantine was caused by a merge-queue restore, while the preserved module
compiles cleanly against the current dependencies. No statement or DAG correction is
needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
