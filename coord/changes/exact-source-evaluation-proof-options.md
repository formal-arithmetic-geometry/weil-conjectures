# AlgebraicGeometry.exists_exactSource_evaluation_open_models

## Reason

The completed reduction needs local sheaf tensor instances and transparent type
comparison during elaboration. The static interface checker classifies file-level
options and local attributes as an interface change, so this record documents them.
No existing declaration signature, visibility, definition, or target meaning changes.
There are no forced adaptations.

## Old

```lean
set_option backward.isDefEq.respectTransparency.types false
```

No local monoidal/symmetric attribute and no scoped heartbeat option preceded the
existing theorem. Its complete original signature is retained verbatim in the
sandbox module; the changes below affect only elaboration of its proof.

## New

```lean
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
```

The theorem also has a scoped `set_option maxHeartbeats 400000 in`, documented by
its adjacent comment. The single-file wall-clock limit remains unchanged. The
attributes are local; importers do not gain instances. The complete existing
signature and standard derived-category instance are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons | unclaimed in local claim snapshot | Unchanged theorem signature and definitions; no adaptation needed. |

This is the only direct importing library module. Transitive users see the same
public declarations and definitions. No imported statement is changed.

## Status

landed 20261013T153936-L-1123777 2026-10-13 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels)
