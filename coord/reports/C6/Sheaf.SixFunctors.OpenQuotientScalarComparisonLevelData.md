## What changed

Constructed the finite-level comparison isomorphisms by whiskering `tc.ordinary` with
scalar restriction, composing with `sc.finite`, and applying
`NatIso.mapHomologicalComplex`. The component equation is definitional. Added the
proof-only module `Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition` for the
strict successor transition calculation and used it to fill the parent structure.

## Proved and sorry left

The level construction and component field of
`openQuotientScalarComparisonLevelData` are proved. Its transition field is discharged
from `openQuotientScalarComparisonTransition`. The latter remains a named `sorry`, with
node `lem-sf-open-quotient-scalar-comparison-transition`; this is one split-off hole.

## No longer needed

No imports or declared dependencies were pruned. The direct data dependency remains
needed for the level construction and the new transition node is used by the parent.

## Where the brief, the DAG or earlier work was wrong

The original proof step combined the explicit finite-level construction with the strict
successor coherence argument. The construction is a direct categorical composition;
the remaining generator calculation is isolated as a strictly smaller theorem. No
target statement or existing definition was changed.

## New nodes

`lem-sf-open-quotient-scalar-comparison-transition` records the successor transition
coherence theorem used by the parent. Its Lean module is
`lean/Sheaf/SixFunctors/OpenQuotientScalarComparisonTransition.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData": "a02014747ab87b117b52907bce21c7efd85fd0bb", "Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition": "8f746f63f296edeed0ccb04b0372f85457ce035e"}, "results": {}, "time": "2026-10-28T06:45:48+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
