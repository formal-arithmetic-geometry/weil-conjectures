# ordinaryProperForgetComparison

## Reason

The repair restores the source module required by the assigned theorem's public import. The module was present in the returned packet but absent from the current published tree, causing the landing gate to reject the import.

## Old

No module was present in the current tree.

## New

`ordinaryProperForgetComparison A f : rightDerivedLowerShriek (ModuleCat A) f ≅ ordinaryFinitePushforward A f`, defined as the existing canonical `rightDerivedLowerShriekIsoRightDerivedLowerStar`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports | R8 | Restores the public comparison used in the target statement. |
| Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupportsUnit | R8 | Restores the public comparison used in the coefficient-free reduction. |

## Status

landed 20261027T180756-L-3900471 2026-10-27 (merge of deliver/R8/Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports)
