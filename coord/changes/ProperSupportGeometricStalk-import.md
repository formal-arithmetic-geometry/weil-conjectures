# ProperSupportGeometricStalk imports and proof interface

## Reason

The proof of the existing support-image declaration now uses the new core theorem module.
The added import is proof-facing and is required for the declaration to compile.

## Old

`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk` did not import
`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore` and left
`properSupport_geometricStalk_image` as `sorry`.

## New

`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk` imports
`Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore` and proves
`properSupport_geometricStalk_image` from its injectivity and range theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperSupportSheafComposition | unclaimed | sees the proved support-image declaration through the existing import |

## Status

landed 20261018T091359-L-3253746 2026-10-18 (merge of deliver/E2/Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk)
