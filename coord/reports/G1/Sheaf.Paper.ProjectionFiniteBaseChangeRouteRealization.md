## What changed

Restored the quarantined dependency `ProjectionFiniteBaseChangeCoordinates` in the
sandbox and repaired `ProjectionFiniteBaseChangeRouteRealization` to import it. Added
strictly smaller left and right route-calculation theorem modules. The item theorem
now combines those two coordinate equations into its required conjunction.

## Proved and sorry left

The item theorem `sixFunctorProjectionFinite_routes_realization` is proved by applying
the two route-calculation declarations. The new declarations
`sixFunctorProjectionFinite_left_route_calculation` and
`sixFunctorProjectionFinite_right_route_calculation` remain as named split-off
`sorry` theorems, one for each coordinate calculation.

## No longer needed

No proof imports were removed. The old bad-import state was repaired by restoring the
existing `Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates` dependency. The original
single conjunction calculation is replaced by the two strictly smaller coordinate
calculations; no other DAG nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The global build's quarantined source had a bad import because the dependency was also
quarantined. The route theorem's calculation is too large to close from the currently
available declarations in this session, so it is decomposed into separate left and
right coordinate calculations. The combining proof is complete and the two split
statements are strictly simpler than the original conjunction.

## New nodes

`lem-sf-finite-base-change-left-route-calculation` is the left coordinate equation;
its source calculation is the first route paragraph of
`prop-sf-pf-coherence.proof.md`.

`lem-sf-finite-base-change-right-route-calculation` is the right coordinate equation;
its source calculation is the second route paragraph of
`prop-sf-pf-coherence.proof.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation": "15feece971c0e5a43a0253a1e6cd274b77b7f207", "Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation": "4d78d29f39de131c0068a188405e0c3b3858927f", "Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization": "a46693bca366a591550afd0f6597350b729e6f8f"}, "results": {}, "time": "2026-10-28T00:59:42+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
