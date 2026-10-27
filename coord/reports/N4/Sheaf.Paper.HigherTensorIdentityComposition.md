## What changed

Completed the existing proof of `WeilConjectures.higherTensor_identityComposition` using
whole-system integral tensor and pullback composition, rational localization, and
common-stage coefficient transport. The theorem statement is unchanged. The proof
uses private categorical transport helpers and retains all identity equality transports.

The module compiles against the current shared snapshot with `lcompile.py` in 52.7
seconds and has no remaining `sorry` declarations.

## Proved and sorry left

Closed the one original hole in `WeilConjectures.higherTensor_identityComposition`
(node `lem-sf-higher-tensor-identity-composition`). Added zero holes and zero new
nodes. No `sorry` remains in the delivered module.

## No longer needed

The original proof-plan dependency `lem-pur-derived-pullback-tensor-iso` is not
used directly. The proof instead uses whole-system tensor composition and the
integral/rational/common-stage comparison APIs. No public imports were removed and
no module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery had the complete proof but was returned because its dependency
imports were absent from the landing snapshot. Those dependency modules are now
available, and the same proof compiles unchanged against the current snapshot. The
DAG proof plan was therefore updated to record the actual whole-system and scalar
transport dependencies used by the proof.

## New nodes

None.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
