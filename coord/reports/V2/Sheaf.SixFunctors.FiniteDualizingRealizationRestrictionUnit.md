## What changed

Filled `WeilConjectures.finiteDualizingRealizationRestriction_unit` with a proof. The
proof unfolds the realization restriction, rewrites the comparison-site identity
restriction using `fd_derivedRestrictionUnit'`, applies the intrinsic identity
coherence theorem at the comparison object, and cancels the derived identity
isomorphisms. Removed the unused `Sheaf.Paper.NormalizedOriginComparisonCoherence`
import. Updated the item's DAG proof dependencies to include
`lem-coef-dualizing-realization-restriction-unit-intrinsic`.

## Proved and sorry left

The theorem `WeilConjectures.finiteDualizingRealizationRestriction_unit` is proved.
No `sorry` remains in the item module and no new `sorry` was added.

## No longer needed

The import `Sheaf.Paper.NormalizedOriginComparisonCoherence` was unused because the
module's local comparison proof and the imported finite-coefficient restriction
API suffice. No declared proof dependency is otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof dependencies omitted the intrinsic identity coherence node,
which is required by the proof; the node copy now records that dependency. No other
issue was found.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit": "73864116e2ca026174da4afad14d67fdb78d1445"}, "results": {"Sheaf.SixFunctors.FiniteDualizingScalarRealization": {"hash": "08374770589942deed8468aff467c0b2c3d5f9bc", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T08:08:21+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
