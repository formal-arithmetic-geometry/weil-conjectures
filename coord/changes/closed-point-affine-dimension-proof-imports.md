# Sheaf.AlgebraicGeometry.ClosedPointAffineDimensionData

## Reason

The statement only uses scheme ring stalks, not presheaf module stalk functors.
Remove the unused public import of the latter. Add the proof-only PointCount import
for its proved finiteness theorem and functoriality equation. No declaration or
statement changes; no target changes meaning.

## Old

```lean
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.RingTheory.Jacobson.Ring
```

## New

```lean
import WeilConjectures.PointCount
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ClosedPointAffineDimensionData`
reports zero downstream modules. A source search also found no importers or
references outside the item, including quarantined files. The item remains needed
by its DAG parents and is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedPointAffineDimensionData | P2 | proof completed; unused public import removed |

## Status

landed 20261023T105414-L-3554711 2026-10-23 (merge of deliver/P2/Sheaf.AlgebraicGeometry.ClosedPointAffineDimensionData)
