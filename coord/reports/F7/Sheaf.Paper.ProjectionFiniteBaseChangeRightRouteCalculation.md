## What changed

The item theorem is proved by reducing the right route to the left route and
rewriting the fixed scalar diamond. The item imports
`Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath` and
`Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality`. Two strictly smaller
normalization statements were split into those modules, each with its own DAG
node.

## Proved and sorry left

Proved `WeilConjectures.sixFunctorProjectionFinite_right_route_calculation`.
The delivery adds the following two named `sorry` theorems:

- `WeilConjectures.sixFunctorProjectionFinite_right_left_path`, node
  `lem-sf-finite-base-change-right-left-path`.
- `WeilConjectures.sixFunctorProjectionFinite_diamond_equality`, node
  `lem-sf-finite-base-change-diamond-equality`.

## No longer needed

No imports or proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The original proof step combined route normalization, fixed-coordinate diamond
identification, and endpoint realization in one statement. The delivery records
the first two as separate strictly smaller intermediate statements so the final
route calculation is a real composition of those steps with the existing left
route calculation.

## New nodes

`lem-sf-finite-base-change-right-left-path` records equality of the right and
left route composites before endpoint realization.

`lem-sf-finite-base-change-diamond-equality` records equality of the two fixed
scalar diamonds.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality": "86a9e4aa642025656934ed6be8d2f91aed4bbe38", "Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath": "21771c09496ddd48b95e713e1505e09da485adcb", "Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation": "278357749265f9d219c14a6cc1388994cfcccc6e"}, "results": {}, "time": "2026-10-28T04:36:31+0800", "transitive": 0, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
