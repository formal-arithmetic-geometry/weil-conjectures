## What changed

Restored the quarantined item module and split the endpoint comparison data into
`integralOrdinaryProjection_endpointComparisons`. The original arrow comparison is now
proved by `Arrow.isoMk` from those endpoint isomorphisms and their commuting square.

## Proved and sorry left

Proved `WeilConjectures.integralOrdinaryProjection_reduction_arrowComparison`.
Added one strictly lower split-off theorem, `WeilConjectures.integralOrdinaryProjection_endpointComparisons`,
with one `sorry`; node `lem-sf-ordinary-projection-endpoint-comparisons`.

## No longer needed

No imports or declared proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The prior global build quarantined this item because the adopted coefficient-change import
was unavailable. The item itself compiles against the published artifacts; the endpoint
comparison is the remaining proper/open scalar argument.

## New nodes

`lem-sf-ordinary-projection-endpoint-comparisons` records the source and target endpoint
isomorphisms and the projection square equation needed by `Arrow.isoMk`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison": "8e88b1754eb1f9d457afc36ee38bb9b0c946b5ad"}, "results": {"Sheaf.Paper.IntegralOrdinaryProjectionReduction": {"hash": "defccef12cd36c480b4604856351d0e79d64be4d", "status": "OK"}}, "seconds": 151, "time": "2026-10-28T01:10:35+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
