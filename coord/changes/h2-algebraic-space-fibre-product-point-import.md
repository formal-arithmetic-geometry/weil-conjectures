# Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint public imports

## Reason

The theorem already expands equality of field-valued point classes as compatible
maps from one field spectrum. Neither its signature nor the completed proof uses
`IsJointlySurjective`, so the public import of its defining module is unnecessary.
Remove it as required by stage-3 import pruning. No declarations or signatures change.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
```

## New

The preceding import is removed. All existing declarations and their signatures stay
identical. The replacement proof uses private Mathlib proof imports.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint --uses
AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective` lists one downstream user of
the affected declaration. The other rows below are all three direct importers of
the item, checked explicitly. No adaptations are necessary or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover | unclaimed (no module claim file) | Already publicly imports AlgebraicSpaceJointSurjectivity itself; its one use of IsJointlySurjective is unaffected. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover | unclaimed (no module claim file) | Imports the item privately; no use of IsJointlySurjective. Its public PointClasses import also provides the algebraic-space point API. |
| Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme | unclaimed (no module claim file) | Imports the item privately; no use of IsJointlySurjective. |
| Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood | unclaimed (no module claim file) | Imports the item privately; no use of IsJointlySurjective. |

Because every direct importer uses a private import of this item, this removal does
not change the public imports of any of those modules. The sole downstream use of
the removed declaration has its own direct public import. No target definition or
target statement is affected; no statement review is reopened.

## Status

landed 20261023T102857-L-2996425 2026-10-23 (merge of deliver/H2/Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint)
