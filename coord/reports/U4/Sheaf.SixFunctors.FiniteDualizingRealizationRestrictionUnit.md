## What changed
Added fully proved comparison-site identity helpers and a new intrinsic identity coherence module. The target is reduced to the intrinsic coherence statement.

## Proved and sorry left
Proved local helpers `fd_ordinaryRestrictionUnit` and `fd_derivedRestrictionUnit`. The target theorem `finiteDualizingRealizationRestriction_unit` remains sorry. New theorem `finiteDualizingIntrinsicRestriction_unit` remains sorry in its new module.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG proof text omits the intrinsic identity coherence between the chosen section-normalized comparison and the normalized DVR identity unit.

## New nodes
`lem-coef-dualizing-realization-restriction-unit-intrinsic` records the strictly lower intrinsic coherence step.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionUnit": "511ecdf44d50d3985da3f78817c34fca42da85b0", "Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionUnit": "e75f4eb6d547f5b0975e3aa1930fbd4515b24e8a"}, "results": {"Sheaf.SixFunctors.FiniteDualizingScalarRealization": {"hash": "08374770589942deed8468aff467c0b2c3d5f9bc", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T07:02:27+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
