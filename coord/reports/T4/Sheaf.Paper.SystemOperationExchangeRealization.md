## What changed

Closed `WeilConjectures.FrobeniusExchange.systemPullEvaluationOrdinaryInv_isIso`
using the existing `SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso`.
Added its module as a proof-only import. The actual sequence ring map, finite constant ring map,
evaluation identifications and original adjunctions specialize the generic theorem exactly;
the direct-image square is the existing `systemDirectEvaluationOrdinary_eq`.
No declaration signature or definition changed. Updated the item's DAG proof dependency and step.

## Proved and sorry left

Closed 1 of the original 11 holes:
`WeilConjectures.FrobeniusExchange.systemPullEvaluationOrdinaryInv_isIso`.
Added 0 holes; no split-off statements.

The following 10 existing holes remain, all attached to
`def-weil-system-operation-exchange-realization`:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`
- `WeilConjectures.FrobeniusExchange.directImage_roos`
- `WeilConjectures.FrobeniusExchange.directImage_linear`
- `WeilConjectures.FrobeniusExchange.directAlpha_isIso`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`
- `WeilConjectures.FrobeniusExchange.compactAlpha_isIso`

## No longer needed

None. No original import, node, module or unit-route step is withdrawn.
The new proof uses one existing generic theorem instead of rebuilding its coextension argument.

## Where the brief, the DAG or earlier work was wrong

The remaining inverse-image evaluation obligation was already covered by the generic
sequence-module pullback evaluation theorem, which was absent from the item's proof imports.
During this session its shared source was updated to remove its former section-normalization
hypothesis. The server initially exposed the old cached signature; the current source dependency
was compiled together with the item to check the specialization against the current interface.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
