## What changed

Removed the redundant public import of
`Sheaf.Paper.RationalPurityExchangeEndpointData`. The item already imports
`Sheaf.Paper.RationalPurityExchangeEndpoints`, which publicly re-exports the
endpoint-data declarations used by this file's public signatures. The restored
module therefore compiles with the same declarations and proof bodies while
avoiding the stale direct import involved in the rework build failure.

## Proved and sorry left

No existing `sorry` was closed. The existing split-off `sorry` remains in
`normalizedExchangeData`, corresponding to
`lem-pur-smooth-exchange-normalized-data`; no new `sorry` was added.

## No longer needed

The direct import `Sheaf.Paper.RationalPurityExchangeEndpointData` is no longer
needed because it is already a public transitive import of
`Sheaf.Paper.RationalPurityExchangeEndpoints`. No DAG nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The rework record reported bad imports after the dependency quarantine. Once the
dependencies were restored, the module compiled. The remaining direct endpoint
data import was redundant and was removed as the local repair; all declarations,
including the documented normalization split, remain unchanged.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SmoothExchangeScalarCompatibility": "76f62584def004aa36d0e2333542696ba6877cd5"}, "results": {}, "time": "2026-10-28T09:42:03+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
