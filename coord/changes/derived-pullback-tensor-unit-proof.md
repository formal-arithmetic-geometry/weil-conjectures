# derivedPullback_tensor_unit proof imports and local helpers

## Reason
The proof replaces the target sorry with explicit construction and transport helpers. The
module's proof-only imports and local universe parameters/attributes necessarily change.

## Old
The target theorem had proof `by sorry`, publicly imported
DerivedPullbackTensorComparisonDescent, and privately imported KFlat,
KFlatResolution, DerivedPullback, and DerivedTensorStructure directly.

## New
The theorem has a complete proof using DerivedPullbackTensorUnitKFlat,
DerivedPullbackTensorUnitCounit, KFlatResolution, and OplaxOfLaxSquare, with private
left/right transport helpers and local universes for the generic monoidal argument.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit | H4 | proof-only imports and private helpers |

## Status

landed 20261012T232858-L-2041709 2026-10-12 (merge of deliver/H4/Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit)
