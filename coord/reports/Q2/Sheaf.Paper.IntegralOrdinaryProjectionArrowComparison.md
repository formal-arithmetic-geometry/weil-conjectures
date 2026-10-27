## What changed

The parent arrow comparison now obtains endpoint isomorphism data and applies a separate pasted compatibility theorem before constructing `Arrow.isoMk`. Added the two proof-dependency modules `IntegralOrdinaryProjectionEndpointIsoData` and `IntegralOrdinaryProjectionEndpointCompatibility`, with matching DAG nodes. The change record is `coord/changes/Q2-integral-ordinary-projection-endpoint-split.md`.

## Proved and sorry left

The existing `integralOrdinaryProjection_reduction_arrowComparison` proof is complete. The endpoint construction remains as the named theorem `integralOrdinaryProjection_endpointIsoData` with one `sorry`, and the pasted compatibility remains as `integralOrdinaryProjection_endpointCompatibility` with one `sorry`.

## No longer needed

None. The parent still uses its existing statement dependencies through the two split endpoint steps.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated the endpoint comparison and its compatibility equation as one opaque hole. The current node plan separates the endpoint construction from the final pasting equation so each is independently reviewable.

## New nodes

- `lem-sf-ordinary-projection-endpoint-iso-data-q2`
- `lem-sf-ordinary-projection-endpoint-compatibility-q2`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionArrowComparison": "25178b2a123b5f9384b4b04ce4c01716b1353d5c", "Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility": "a6928487525850336f2be911836f452950a2a776", "Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData": "0b24386c65ea5a1d6c8ede0a2fa43847d915e76d"}, "results": {"Sheaf.Paper.IntegralOrdinaryProjectionReduction": {"hash": "defccef12cd36c480b4604856351d0e79d64be4d", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T02:59:53+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
