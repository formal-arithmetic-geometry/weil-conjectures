## What changed

Added `Sheaf.Paper.ScalarP1UnitMateComponent`, which isolates the scalar twisted-unit
exchange equation after removing the unused completed Chern data from the component.
The assigned theorem now reduces to this named component theorem by `simpa only`.

## Proved and sorry left

The assigned declaration `scalar_chern_base_change_unit` is closed in the item module.
One strictly smaller categorical component theorem remains as `sorry`:
`scalar_p1_unit_mate_component` in `Sheaf.Paper.ScalarP1UnitMateComponent`.

## No longer needed

The completed Chern normalization hypotheses and the `scalarQChern` and `scalarP2Chern`
let-bindings do not occur in the unit component equation. No proof dependency was
removed from the item import closure.

## Where the brief, the DAG or earlier work was wrong

The original component statement carries completed Chern data that is unused by its
conclusion. The reduction records the unit-only categorical component separately.

## New nodes

`lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core` records the split
categorical component theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit": "08f873cd81d0f4854a29e0778513a4bcf04f613b", "Sheaf.Paper.ScalarP1UnitMateComponent": "01049f6d42cbead1b480ec1a4a02f1ad4aecda67"}, "results": {"Sheaf.Paper.RationalP1ScalarChernBaseChange": {"hash": "2e619fb96d918c194ac32aef46d40e4abed4efe6", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T04:22:02+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
