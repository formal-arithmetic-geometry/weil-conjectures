# SheafOfModules.isGrothendieckAbelian local registration

## Reason

The proof of AlgebraicGeometry.tensorCounit_oneKFlat_coordinates and its private helpers need the already proved Grothendieck instance during elaboration of tensor total complexes and their colimits. Register it locally to avoid repeated expensive instance searches. The static interface checker counts an added attribute command as an interface change, so this record documents its precise scope. No definition or theorem statement changes.

## Old

No local registration of SheafOfModules.isGrothendieckAbelian in namespace AlgebraicGeometry in Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates. The declaration itself is unchanged.

## New

```lean
attribute [local instance] SheafOfModules.isGrothendieckAbelian
```

This registration applies only within the current module's namespace. Importers receive no new instance registration. Existing signatures, visibility and definitions stay identical. The new theorem module uses the same local elaboration convention.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | K3 | Local proof elaboration only; signature unchanged. |
| Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation | new, K3 | Local elaboration of the new theorem statement only. |

No existing downstream module has a semantic dependency changed; no forced adaptation is included. The existing theorem's statement and the target statements retain their meanings.

## Status

landed 20261013T100025-L-2468000 2026-10-13 (merge of deliver/K3/Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates)
