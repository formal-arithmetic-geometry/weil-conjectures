## What changed

Added `Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion`, which isolates the explicit source/target comparison expansion used by the assigned route calculation. The assigned theorem now reduces to that expansion by unfolding `sixFunctorProjectionFiniteLeftPath`. Updated the copied parent DAG node to depend on the expansion node.

## Proved and sorry left

The assigned theorem `WeilConjectures.sixFunctorProjectionFinite_left_route_calculation` is closed by a real reduction to the expansion theorem. One new sorry remains in `WeilConjectures.sixFunctorProjectionFinite_left_route_expansion`; it records the naturality, triangle-identity, and finite pull-composition calculation required by the proof plan.

## No longer needed

No proof-dependency imports were removed. The route uses the coordinate definitions and all three original proof dependencies through the new expansion node.

## Where the brief, the DAG or earlier work was wrong

The original node treated the full expansion and endpoint cancellation as one elementary step, but the direct unfold leaves a substantial naturality calculation. The delivery records that calculation as a strictly lower-level expansion statement while preserving the target theorem unchanged.

## New nodes

`lem-sf-finite-base-change-left-route-expansion` records the explicit expanded composite and its proof source.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation": "d4cc4897b248d9875047df4666dcd051e142c41b", "Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion": "e481d69fbda6eee74b3bcd102333978e437deca7"}, "results": {}, "time": "2026-10-28T04:20:08+0800", "transitive": 0, "version": 1}
```

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
