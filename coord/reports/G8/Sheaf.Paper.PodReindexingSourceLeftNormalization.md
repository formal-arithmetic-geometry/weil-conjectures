## What changed

Replaced the proof hole of `WeilConjectures.PodReindexingCoherence.source_left_normalization`
with the prescribed model calculation. The proof uses the source-site-independent
`LeftNormalization` on X, uniqueness of `LeftFormula`, naturality of the ordinary Hom
comparison, naturality of the derived comparison, and shift compatibility of the exact
localization factors. All added helpers are private and proved. The only additional import
is a proof import of all declarations of `RingedInternalHomShiftOfUniverses`, giving access
to its proved private uniqueness and naturality lemmas. Existing statements and public
imports are preserved.

Validation: the complete proof compiled through `lcompile.py` in 54.1 seconds.
The heartbeat-setting comment requested by the style linter was then added; delivery
checks compile the final version. The theorem signature matches the original verbatim
up to whitespace.

## Proved and sorry left

Closed: `WeilConjectures.PodReindexingCoherence.source_left_normalization`
(node `lem-pod-reindexing-source-left-normalization`), the one original hole.
Added holes: none. Remaining holes in the delivery: none. No decomposition or new nodes.

## No longer needed

None. All five recorded proof dependencies are used through the existing model-factor
import and the proof import. No modules, nodes, declarations, or imports are withdrawn.
The proof does not require the other source-shift route or the chain reindexing square.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing full representative normalization
and the Mathlib `NatTrans.CommShift` instance for `mapDerivedCategoryFactors.hom`
suffice to carry out the stated plan without another split. The blueprint unit route and
the assigned statement are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingSourceLeftNormalization": "d31c93b9dec330f05e6aabcdfae674b59aea0185"}, "results": {"Sheaf.Paper.PodReindexingDerivedSourceShiftModel": {"hash": "56106e7b2b8a800d2e55fcd9e35026b6c315017f", "status": "OK"}}, "seconds": 121, "time": "2026-10-28T14:28:29+0800", "transitive": 0, "version": 1}
```

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
