# etaleTensorSectionsTransparency

## Reason
The identity proof needs local transparency controls to keep elaboration within the file limit.
The controls are proof-local attributes/options and do not alter declarations or definitions.

## Old
No local transparency controls.

## New
`attribute [local irreducible] tensorPullback tensorPullbackObj` and scoped transparency options
around the identity proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleTensorSections | G2 | proof elaboration only |

## Status
landed 20261012T085242-L-15771 2026-10-12 (merge of deliver/G2/Sheaf.AlgebraicGeometry.EtaleTensorSections)
