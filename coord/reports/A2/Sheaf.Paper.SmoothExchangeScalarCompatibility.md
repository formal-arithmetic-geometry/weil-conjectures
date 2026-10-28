## What changed

Removed the redundant public import `Sheaf.Paper.RationalScalarComparisonData` from
`Sheaf.Paper.SmoothExchangeScalarCompatibility`. The module already receives the
same declarations through the public imports `Sheaf.Paper.RationalPurityExchangeEndpoints`
and `Sheaf.Paper.TwistedPullbackSquareScalars`; all declarations and proof bodies
are otherwise unchanged. The module compiles against the current dependency chain.

## Proved and sorry left

No existing sorry was closed. The single existing sorry remains in
`normalizedExchangeData`, corresponding to `lem-pur-smooth-exchange-normalized-data`.
No new sorry was added.

## No longer needed

The direct public import `Sheaf.Paper.RationalScalarComparisonData` is no longer
needed because its declarations are re-exported by the endpoint dependency. No DAG
nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The rework record reported stale bad imports from the dependency quarantine. After
restoring the current item source, the only remaining redundant direct import was
`RationalScalarComparisonData`; removing it leaves the module compiling and keeps the
existing normalized-data split unchanged.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SmoothExchangeScalarCompatibility": "557dbb33c022a764ac0955c2325c097139d98e67"}, "results": {}, "time": "2026-10-28T10:04:14+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
