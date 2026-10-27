# Sheaf.AlgebraicGeometry.FundamentalGroup.PointedCoverCompatibleUnitRoots

## Reason

The item definitions need the existing `UniversalCover.cover`, `proj`, and `pt` from the source construction. Its proof needs the already proved `toObj` section and connectedness from that same source module. The larger `PointedLimitCech` package is unnecessary: no Cech coordinates, profinite group, or group action is used. Replace the public import with its actual defining source so the item does not expose or depend on unrelated Cech coordinate statements. The three public definitions and the public theorem retain their exact signatures and bodies except for the completed theorem proof.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FundamentalGroup.PointedCoverCompatibleUnitRoots --uses AlgebraicGeometry.Scheme.UniversalCover.pointedCover_compatible_unit_roots` reports zero downstream modules on the delivery base. Direct import search likewise finds none. No consumer needs adaptation. Pending DAG parents still receive exactly the same pointed cover, ring maps, root theorem, and tame-order type; no node is withdrawn and no mathematical statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PointedCoverCompatibleUnitRoots | D3 | Same declarations, proved theorem, minimal public source construction import. |

## Status

landed 20261023T123426-L-1186742 2026-10-23 (merge of deliver/D3/Sheaf.AlgebraicGeometry.FundamentalGroup.PointedCoverCompatibleUnitRoots)
