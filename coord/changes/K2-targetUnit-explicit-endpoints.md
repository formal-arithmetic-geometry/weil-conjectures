# WeilConjectures.ConcreteIntegralProjection.targetUnit

## Reason

Write the identical endpoints explicitly to avoid inferring them through large functor constructions. The map and its meaning are unchanged by definitional equality; no consumer is adapted. Target meanings are unchanged; the independent review can check the displayed constructions.

## Old

```lean
def targetUnit
    (aX : SfProEtaleProjection.TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  (image (completed l E) c).map ((IntegralOnSlice.completionUnit l E X none).app
    (SfProEtaleProjection.ordinaryInner l E f aX K L))
```

## New

```lean
def targetUnit
    (aX : SfProEtaleProjection.TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    (image (completed l E) c).obj (SfProEtaleProjection.ordinaryInner l E f aX K L) ⟶
      SfProEtaleProjection.completedTarget l E c aX K L :=
  (image (completed l E) c).map ((IntegralOnSlice.completionUnit l E X none).app
    (SfProEtaleProjection.ordinaryInner l E f aX K L))
```

## Users

`tools/downstream.py Sheaf.Paper.ConcreteIntegralProjectionCone --uses targetUnit` lists only the item itself, with zero downstream importing modules. Unfinished DAG parents still retain the item and its original statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | K2 | Identical endpoint types and actual map; explicit proof unfolding. |

## Status

landed 20261026T023420-L-563644 2026-10-26 (merge of deliver/K2/Sheaf.Paper.ConcreteIntegralProjectionCone)
