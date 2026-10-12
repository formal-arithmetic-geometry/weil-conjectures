# Sheaf.AlgebraicGeometry.AffineBaseChangeTensorComparisons imports

## Reason

The theorem's statement uses tensorPullback and exists_tensorPullbackAdjunction,
not moduleBaseChangeMap or its open-restriction theorems. Import the adjunction
module directly, avoiding the unused open-restriction module. This changes the
public import surface but no declaration signature or definition.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange | unclaimed in this delivery; not modified | No effect: it already directly public-imports ModuleBaseChangeMapOpenRestriction, TensorPullbackStructureSheaf and ModulePullbackTensor. No forced adaptation. |

This is the only direct importer, found by searching the whole lean/ source tree.
Its statements and definitions retain all their original dependencies, so all
transitive users and target meanings remain unchanged. No target review reopens
because no definition changes.

## Status

landed 20261012T135223-L-1658072 2026-10-12 (merge of deliver/D2/Sheaf.AlgebraicGeometry.AffineBaseChangeTensorComparisons)
