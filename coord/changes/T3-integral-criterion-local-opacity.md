# integralSectionAbIdentifications: file-local opacity for upperStarFromPoint

## Reason

Endpoint identification uses congruence for the point inverse-image functor. Without
local opacity, elaborating that congruence unfolds upperStarFromPoint and exceeds
200000 heartbeats. With local opacity the delivery module compiles in 4.0 seconds.
The setting is local to this file, is not exported to importers, and changes neither
the definition of upperStarFromPoint nor any theorem signature. This record is
provided because the static delivery gate classifies a new attribute command as
requiring a change record, even when the command explicitly says local.

## Old

No file-local opacity command for upperStarFromPoint in this module.

## New

```lean
attribute [local irreducible] upperStarFromPoint
```

All existing definitions and public signatures are unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralCriterionReductions --uses
integralSectionAbIdentifications` reports two downstream modules, and only the item
itself mentions this theorem. The local attribute does not propagate to either importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCriterionReductions | T3 | Avoids unfolding in endpoint congruence. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | Unchanged, see current claims | None; no exported signature or attribute changes. |
| Sheaf.Paper.IntegralSectionLocalModels | Unchanged, see current claims | None; no exported signature or attribute changes. |

No consumer adaptation is needed: all theorem types, definition bodies and public imports
are preserved. No target statement or target-used definition is changed.

## Status

landed 20261021T194249-L-1528130 2026-10-21 (merge of deliver/T3/Sheaf.Paper.IntegralCriterionReductions)
