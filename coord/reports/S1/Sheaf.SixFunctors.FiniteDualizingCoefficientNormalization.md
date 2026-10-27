## What changed

The proof of `WeilConjectures.finiteDualizing_compact_normalization` now introduces
its four conjuncts from the already stated lower-level normalization theorems.  It
uses `finiteDualizing_compact_support_identity` for the first conjunct and
`finiteDualizing_quotient_normalization` for the remaining three.  The existing
public `FiniteDualizingData` import and theorem statement are unchanged; the two
normalization imports remain proof-only imports.

## Proved and sorry left

The single sorry in `finiteDualizing_compact_normalization` is closed.  No new
sorry is added.  The two imported lower-level declarations retain their existing
sorries: `finiteDualizing_compact_support_identity` and
`finiteDualizing_quotient_normalization`; they are strictly smaller conjunction
components and are recorded by nodes `lem-coef-dualizing-compact-support-identity`
and `lem-coef-dualizing-quotient-normalization`.

## No longer needed

None.  The proof uses both split modules and the definitions exposed by
`FiniteDualizingData`.

## Where the brief, the DAG or earlier work was wrong

The earlier split made the parent theorem a conjunction of the two lower-level
normalization statements.  Once those declarations are imported, the parent is
proved by direct conjunction introduction and no additional mate calculation is
needed here.  The DAG proof dependencies were therefore updated from the generic
mate dependencies to the two actual split nodes used by the Lean proof.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization": "67ac51c63df58fad88a4d883161231de215ed32a"}, "results": {}, "time": "2026-10-28T06:40:20+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
