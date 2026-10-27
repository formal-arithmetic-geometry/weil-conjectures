## What changed

Added `FiniteTorOrdinaryPullCompleteFixedDatum.lean`, isolating the fixed finite-field-datum Roos transport required by ordinary pullback completeness. The target theorem now unfolds the global slice predicate, applies that fixed-datum theorem to its witness, and repackages the witness. The target node copy records this proof route.

## Proved and sorry left

Closed `finiteTorOrdinaryPullComplete_of_complete` (1 of 1 original sorry). Added one strictly smaller intermediate statement, `finiteTorOrdinaryPullComplete_fixed_datum`, whose proof remains `sorry` for the fixed-datum Roos transport step.

## No longer needed

No imports or declared proof dependencies were removed. The original direct proof route was unavailable because the ringed pullback changes the completed coefficient module category; the target therefore uses the fixed-datum reduction.

## Where the brief, the DAG or earlier work was wrong

The target DAG proof text omits the necessary fixed finite-field-datum transport theorem and gives no public declaration for the levelwise Roos comparison. The existing declarations define completeness as an existential over such a datum, so the target can only be reduced to that strictly smaller transport statement from the available interfaces.

## New nodes

- `lem-sf-finite-tor-ordinary-pull-complete-fixed-datum`: fixed finite-field-datum preservation of `IsDerivedComplete` under the ordinary ringed pullback; declared in `Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteFixedDatum`.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
