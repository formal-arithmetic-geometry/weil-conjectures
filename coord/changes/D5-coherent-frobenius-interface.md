# coherent_frobenius_comparison public dependency import

## Reason

The restored item has a forced adaptation of the held module
`Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback`. Stage-3 delivery checks require
an item's own interface change when adapting a module held by another group. The
comparison theorem's public interface therefore exposes the unchanged
`CoherentFrobeniusPullback` module import. This makes the dependency available to
importers of the comparison theorem while leaving every declaration signature and
proof unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
import Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | D5 | public dependency import and redundant canonical import removal make the forced adaptation reviewable |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | A2 | adapted module remains compilable through the public dependency path |

## Status

landed 20261020T235550-L-1189935 2026-10-20 (merge of deliver/D5/Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison)
