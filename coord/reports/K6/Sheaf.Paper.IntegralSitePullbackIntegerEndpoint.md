## What changed

Proved `integral_site_pullback_integer_endpoint` by applying the generic four-adjunction
conjugate-mate lemma, cancelling the invertible comparison maps, and identifying the
pro-etale inverse-image map with the adjoint of the constant direct-image map. Added the
named mate and inverse-image substeps as separate modules.

## Proved and sorry left

Closed `integral_site_pullback_integer_endpoint`. Added two named split theorems:
`integral_site_pullback_integer_endpoint_mate` and
`integral_site_pullback_integer_endpoint_inverse_image`; both proofs remain `sorry`.

## No longer needed

None. The existing imports are used by the endpoint and mate modules.

## Where the brief, the DAG or earlier work was wrong

The endpoint proof plan omitted the concrete comparison-mate equality needed before the
final cancellation. That equality is recorded as the new mate node.

## New nodes

`lem-sp-integral-site-pullback-integer-endpoint-mate` and
`lem-sp-integral-site-pullback-integer-endpoint-inverse-image`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralSitePullbackIntegerEndpoint": "cd793f4311d81e32553b59c83c86ab41de86328c", "Sheaf.Paper.IntegralSitePullbackIntegerEndpointInverseImage": "1e3c9c819179d532357cb5623f554435d66bb0a5", "Sheaf.Paper.IntegralSitePullbackIntegerEndpointMate": "6c323a1b7909497148d0a6d92f638608ff4563fa"}, "results": {}, "time": "2026-10-28T05:34:41+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
