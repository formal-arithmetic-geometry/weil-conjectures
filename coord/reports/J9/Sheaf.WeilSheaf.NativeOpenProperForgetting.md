## What changed

Closed the `proper_frobenius` proof in `Sheaf.WeilSheaf.NativeOpenProperForgetting` by definitional
reduction: both localized maps are the same degreewise Frobenius structure map, so `rfl` proves the
stated equality. No imports, declarations, or statements were changed.

## Proved and sorry left

Proved: `AlgebraicGeometry.NativeWeilOpenProper.proper_frobenius` (one existing sorry closed).

Sorries left in the item: `AlgebraicGeometry.NativeWeilOpenProper.hearts`,
`AlgebraicGeometry.NativeWeilOpenProper.proper_normalization`, and
`AlgebraicGeometry.NativeWeilOpenProper.open_proper`. No new sorries were added.

## No longer needed

None. The module's existing imports remain because the other open proofs still follow the recorded
route.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeOpenProperForgetting": "0bce64bc4bd5f90510f2ffb35b9487ad83d02bf1"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalHomTransport": {"hash": "b1bfb8088d3ec79a7fe43d0f8a201a0ae6d86776", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T04:15:51+0800", "transitive": 0, "version": 1}
```

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
