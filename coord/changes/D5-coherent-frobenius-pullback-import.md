# Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback imports

## Reason

The comparison item imports `CoherentFrobeniusPullback`. Against the current
published build, that module's private import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge` fails before
its theorem can be used: the published edge object contains the old Sheaf copy of
`ExtEdgeResolution.moduleComparisonEquiv`, while importing its upstream naturality
module tries to declare the same constant again. The edge import is not used by the
current theorem statement or its sorry proof. Removing that private import lets the
adapted dependency compile and leaves every public declaration and signature
unchanged.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
```

## New

The line above is removed. All other imports, declarations, visibility, and theorem
signatures in `CoherentFrobeniusPullback` are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | A2 | forced adaptation: remove one private import that prevents compilation against the current published build |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | D5 | imports the adapted module and uses its unchanged theorem |

## Status

landed 20261020T235550-L-1189935 2026-10-20 (merge of deliver/D5/Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison)
