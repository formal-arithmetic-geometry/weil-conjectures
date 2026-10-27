## What changed

Kept the repaired direct public import of `Sheaf.Paper.CompactSupportFiniteAction`, which
avoids the historical quarantined `QcqsCompactSupportRealization` dependency. Rewrote the
proof of `systemOpenScalarInv_isIso` using an explicit refinement of
`NatIso.isIso_of_isIso_app`; the theorem and all declarations retain their existing
statements and dependencies.

## Proved and sorry left

No additional theorem hole was closed. The existing proof of
`WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso` remains proved. The six
existing theorem holes remain: `systemDirectEvaluation_isIso`, `systemExchange_evaluation`,
`systemOpenEvaluationInv_isIso`, `systemOpenExchangeInv_isIso`, `directImage_roos`, and
`compactRealization_existsUnique`. The split component theorem
`systemOpenScalarInv_app_isIso` remains the one named split-off obligation. No new `sorry`
was added.

## No longer needed

None. The direct `CompactSupportFiniteAction` import remains required by exposed types and
finite compact-support constructions. No DAG proof dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The recorded bad-import build error is stale: the current source already contains the C7
repair replacing `QcqsCompactSupportRealization` with `CompactSupportFiniteAction`. The
remaining componentwise scalar mate is intentionally represented by its split node.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SystemOperationExchangeRealization": "65cb308ecc7f1a97701cbfb7804a1d5fd64721c5"}, "results": {}, "time": "2026-10-28T07:14:34+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
