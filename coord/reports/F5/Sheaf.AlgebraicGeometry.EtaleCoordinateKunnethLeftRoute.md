## What changed

Proved `AlgebraicGeometry.Etale.CoordinateTrace.coordinateKunneth_leftRoute_comp_kunneth` by rewriting `kunnethMap` with `kunnethMap_eq` and cancelling the canonical right-derived composition isomorphism. Added the private proof import `Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp`, whose pre-composition mate calculation is the remaining split statement.

## Proved and sorry left

Closed the original theorem `coordinateKunneth_leftRoute_comp_kunneth`. Added one strictly simpler split theorem, `coordinateKunneth_leftRoute_precomp`, with node `new-sfb-etale-coordinate-kunneth-left-route-precomp`; its proof remains `sorry` because the categorical mate expansion and coherence are not closed in this delivery.

## No longer needed

The former proof dependencies `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` and `lem-weil-pbc-ringed-exchange-tensor-coherence` are not imported by the completed parent proof; the missing pre-composition calculation is isolated in the new node. No existing declarations or modules were removed.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the pre-composition mate calculation with cancellation by the composition isomorphism. The cancellation is immediate once the pre-composition equality is stated, so the proof has been split at that strictly simpler boundary.

## New nodes

`new-sfb-etale-coordinate-kunneth-left-route-precomp` records the left-route equality before the final composition isomorphism; it is stated in `lean/Sheaf/AlgebraicGeometry/EtaleCoordinateKunnethLeftRoutePrecomp.lean` and remains for a later worker to prove.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute": "5e1041422d90c01b3c5981a9bd8d5b48207d9d4b", "Sheaf.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp": "ed249be1c5213405b4d242177e7b101bf16852a8"}, "results": {}, "time": "2026-10-28T08:30:08+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
