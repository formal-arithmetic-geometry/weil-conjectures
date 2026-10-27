## What changed

Proved `coordinateKunnethFactorization_transpose` by rewriting the two sides with the
pre-pullback coordinate route equality. Added the strictly simpler split theorem
`coordinateKunnethFactorization_route_eq` in its own module.

## Proved and sorry left

Closed `coordinateKunnethFactorization_transpose` (one sorry). Added one sorry in
`coordinateKunnethFactorization_route_eq`, which records the mate calculation below the
target.

## No longer needed

The attempted separate left and right transpose route is not imported: the final proof
uses the smaller pre-pullback route equality directly.

## Where the brief, the DAG or earlier work was wrong

The planned separate adjunction-transpose cancellation is not definitionally stable:
the trace datum `H` presents the tensor route through `derivedTensorRight`, while the
coordinate comparison presents it through the tensor abbreviation. The direct
pre-pullback equality is the shorter valid reduction.

## New nodes

Added `lem-sfb-etale-coordinate-kunneth-route-equality`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose": "72ef0d87f5f802b4528f1ca8951a45bdfbbb83fc", "Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality": "dd727732c14469e5cc29ec7978c13ce79cbb4902"}, "results": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethFactorization": {"hash": "ee49a4731613a4d56b66bdf312553e8e11248490", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T03:23:23+0800", "transitive": 0, "version": 1}
```

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
