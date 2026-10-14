# PuncturedFlasqueResolutionComparison elaboration options

## Reason
The completed proof requires the two local elaboration transparency options below. The
stage-3 static check classifies these commands as changing the module environment seen by
importers, so the change is recorded explicitly.

## Old
```lean
@[expose] public section
universe u
open CategoryTheory
```

## New
```lean
@[expose] public section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionComparison | H1 | The options are required for elaborating the proof; declaration signatures are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionCohomology | unclaimed | Direct importer; its statements and proof continue to use the identical comparison signature. |

## Status
landed 20261014T010842-L-3163640 2026-10-14 (merge of deliver/H1/Sheaf.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionComparison)
