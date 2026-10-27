## What changed

In `Sheaf.Paper.SystemOperationExchangeRealization`, proved
`WeilConjectures.FrobeniusExchange.systemDirectEvaluationOrdinary_eq`.
The private helper `vertical_pushforward_eq` identifies the two composites of
continuous module pushforwards from their coefficient-map equation. At a vertical
slice the coefficient-identification maps are identities, and the system ring map
is the same constant-section map as the finite direct-image ring map.

All existing declaration signatures, definitions and imports are preserved. This
implements the existing theorem docstring's sectionwise proof. The node proof now
records this elementary calculation and the eleven remaining obligations; its
proof dependencies and unit realization are unchanged. No new node is needed.

Validation: the complete module compiled through `lcompile.py` in 38.3 seconds
with exit code zero.

## Proved and sorry left

Closed one of the twelve original holes:
`WeilConjectures.FrobeniusExchange.systemDirectEvaluationOrdinary_eq`.
Added zero holes and split off zero statements. The private helper is proved.

Eleven existing holes remain, all attached to
`def-weil-system-operation-exchange-realization`, in namespace
`WeilConjectures.FrobeniusExchange`:

- `systemPullEvaluationOrdinaryInv_isIso`
- `systemDirectEvaluation_isIso`
- `systemExchange_evaluation`
- `systemOpenEvaluationInv_isIso`
- `systemOpenExchangeInv_isIso`
- `systemOpenScalarInv_isIso`
- `directImage_roos`
- `directImage_linear`
- `directAlpha_isIso`
- `compactRealization_existsUnique`
- `compactAlpha_isIso`

Their statements, complete proof docstrings and whole-theorem sorry bodies are
unchanged. The existing proofs elsewhere in this module are retained.

## No longer needed

None. No imports were removed, and no dependency node or module was pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy found. Direct unfolding of the concrete
pushforward equality exhausted elaboration heartbeats; the abstract coefficient-map
calculation avoids expanding the concrete coefficient constructions.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
