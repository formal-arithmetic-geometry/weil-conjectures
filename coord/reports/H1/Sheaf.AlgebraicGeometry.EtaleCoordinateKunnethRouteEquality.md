## What changed

The item theorem is now proved by cancelling the canonical compositor
`R p₁_* ⋙ R f_* ≅ R (p₁ ≫ f)_*`. Two strictly smaller route calculations were
split into separate modules: the ordered-projection/comparison route and the
projection/exchange route are each identified with the canonical `kunnethMap`
after that compositor. The item imports those modules and combines the two
identifications by transitivity.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunnethFactorization_route_eq`.

The delivery adds these named, documented sorries for the two remaining mate
calculations:

- `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunneth_leftRoute_comp_kunneth`
  (node `lem-sfb-etale-coordinate-kunneth-left-route-comp-kunneth`).
- `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunneth_rightRoute_comp_kunneth`
  (node `lem-sfb-etale-coordinate-kunneth-right-route-comp-kunneth`).

## No longer needed

No imports or declared dependencies were removed. The item now uses the
canonical `kunnethMap` and its direct-image composition isomorphism through the
two split route modules.

## Where the brief, the DAG or earlier work was wrong

The original route plan treated the full coordinate mate calculation as one
module theorem. The available library already exposes the canonical Kunneth
map and its composition interface, so the calculation naturally decomposes into
two independent route-to-Kunneth identities followed by cancellation. No target
statement was changed.

## New nodes

- `lem-sfb-etale-coordinate-kunneth-left-route-comp-kunneth`: route-to-Kunneth
  mate identity for the ordered-projection/comparison route.
- `lem-sfb-etale-coordinate-kunneth-right-route-comp-kunneth`: route-to-Kunneth
  mate identity for the projection/exchange route.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute": "1768e3ba9abef212c9aa987920041a32bf76fe47", "Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute": "186ddc9804ee0d2c1aa72b052b3706a6ae141b5c", "Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality": "c63559c44ed13b8b54669e4612fe49ceb2894f85"}, "results": {}, "time": "2026-10-28T06:40:34+0800", "transitive": 0, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
