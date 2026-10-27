## What changed

Proved `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso` by applying
`NatIso.isIso_of_isIso_app`. The componentwise scalar-open mate calculation is
recorded as the strictly smaller intermediate theorem
`systemOpenScalarInv_app_isIso`, with its proof retained for a follow-up worker.
The current `CompactSupportFiniteAction` import also records the historical import
repair from `QcqsCompactSupportRealization`.

## Proved and sorry left

Closed one existing hole: `systemOpenScalarInv_isIso`.

One new split-off hole remains: `systemOpenScalarInv_app_isIso`.
The six existing holes remain:

- `systemDirectEvaluation_isIso`
- `systemExchange_evaluation`
- `systemOpenEvaluationInv_isIso`
- `systemOpenExchangeInv_isIso`
- `directImage_roos`
- `compactRealization_existsUnique`

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The historical build error named the quarantined
`QcqsCompactSupportRealization` import, but the current source already contains
its repaired `CompactSupportFiniteAction` import. The natural-transformation
invertibility proof reduces cleanly to componentwise invertibility; the latter is
tracked as a separate DAG obligation.

## New nodes

Added `lem-weil-system-open-scalar-inv-app-is-iso` for the componentwise mate
calculation.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 26, "left_out": 0, "own": {"Sheaf.Paper.SystemOperationExchangeRealization": "5818959f5e3a708e096ca8982ae45e09b4add860"}, "own_failed": ["Sheaf.Paper.SystemOperationExchangeRealization"], "results": {}, "time": "2026-10-28T04:13:34+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
