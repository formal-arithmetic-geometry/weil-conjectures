# AlgebraicGeometry.singleComplexOpen_unit_square_factorization

## Reason

The proof and unchanged statement use `singleComplexOpenPullbackIso`, supplied by
`SingleComplexOpenRestrictionData`, but use none of the tensor restriction
comparisons defined by `OpenPinnedSingleDegreeZeroCounitIso`. Import the statement
module directly and prune the unused public import. This is an import-interface
change only: no declaration signature or definition changes, and no target changes
meaning. The proof follows the existing pinned adjunction and naturality route.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
```

## New

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | Sole direct importer. Already publicly imports OpenPinnedSingleDegreeZeroCounitIso itself, so its interface, statement and proof retain all their dependencies without adaptation. |

The `stage3_delivery.downstream_users` check for the import-interface marker returns
no textual declaration users. Inspection of all source imports finds only the row
above as a direct importer. The unchanged theorem uses precisely the same data and
categories, so its existing callers require no adaptation. No extra modules are
included or edited.

## Status

landed 20261014T063822-L-2815434 2026-10-14 (merge of deliver/R3/Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization)
