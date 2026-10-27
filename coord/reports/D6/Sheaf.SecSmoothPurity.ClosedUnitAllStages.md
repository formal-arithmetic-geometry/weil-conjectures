## What changed

The item module now decomposes `closedUnitAllStages` into two named component theorems:
`closedUnitAllStages_exists` supplies the all-stage presentation, and
`closedUnitAllStages_properties` supplies the full-faithfulness and adjunction-unit
properties for a fixed presentation.  The parent theorem combines these components by
an explicit conjunction and function application.  The structures and the target
statement are unchanged; no imports were added or removed.

## Proved and sorry left

The original `WeilConjectures.closedUnitAllStages` hole is closed by a real Lean proof
combining the two strictly smaller components.  Two genuine component holes remain:
`WeilConjectures.closedUnitAllStages_exists` and
`WeilConjectures.closedUnitAllStages_properties`, both in the item module, with nodes
`lem-sf-closed-unit-all-stages-existence` and
`lem-sf-closed-unit-all-stages-properties` respectively.  They carry the construction
and Hom/adjunction arguments as their complete proof plans.

## No longer needed

None.  The module's imports are retained because they provide the declarations used by
the presentation structures and the unchanged public signature.  The parent node's old
proof dependencies are replaced by the two split component nodes.

## Where the brief, the DAG or earlier work was wrong

The prior proof plan asks for a many-stage construction whose intermediate comparison
lemmas are themselves postponed.  This delivery records the two independent conclusions
that are actually needed to assemble the parent conjunction, without weakening the target
or introducing an unconstrained functor.  The current global build error reports three
imports as unavailable, but the required single-file compile resolves those imports and
compiles the module successfully; no source declaration was changed to work around that
stale build report.

## New nodes

`lem-sf-closed-unit-all-stages-existence` records the existence component and its
construction plan.  `lem-sf-closed-unit-all-stages-properties` records the fixed-
presentation full-faithfulness and unit component and its Hom/Yoneda plan.  Both nodes
use the item's chapter and unit and attach to the declarations in
`lean/Sheaf/SecSmoothPurity/ClosedUnitAllStages.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SecSmoothPurity.ClosedUnitAllStages": "9e350bdde7735e61472675326c866fe08c4d7270"}, "results": {}, "time": "2026-10-28T06:51:48+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
