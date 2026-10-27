## What changed

Restored the quarantined `Sheaf.Paper.ConstantPurityFrobeniusSquare` module and
kept its existing four auxiliary proofs and two remaining theorem holes. The
`betaAtStage` construction now gives its common field an explicit
`FieldStage.{u}` type, which avoids the expensive implicit universe/category
elaboration that caused the rework timeout. The category transport proof is
unchanged and remains definitional after unfolding the two published category
constructors.

Validation: `lcompile.py` compiled the complete module successfully in 39.9
seconds. No target statement or declaration signature changed.

## Proved and sorry left

This repair closes no additional theorem holes. The module contains two
remaining named theorem proofs:

- `WeilConjectures.ConstantPurityFrobenius.beta_existsUnique`.
- `WeilConjectures.ConstantPurityFrobenius.constant_purity_frobenius_square`.

The four auxiliary proofs already present in the restored module remain
proved: `chainUnit_existsUnique`, `chainUnit_isIso`,
`rationalExchange_endpoints`, and `exceptionalMate_isIso`. No new `sorry` was
added and no split-off theorem was needed.

## No longer needed

None. The existing proof imports, declarations, and DAG dependencies remain
needed by the two unfinished theorem statements and their parent route.

## Where the brief, the DAG or earlier work was wrong

The rework entry reported a heartbeat timeout in the archived finite-stage
component. The repaired component already separates its conjugation factors
and transports the rational arrow explicitly; adding the explicit universe
level to its local common field removes the remaining costly inference while
preserving the same morphism and statement.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
