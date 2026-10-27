# WeilConjectures.ConcreteIntegralProjection.targetUnit

## Reason

Write the original inferred source and target of this image of the completion unit
explicitly. This avoids expanding the image functor and tensor presentation merely
to infer endpoints. The morphism body is unchanged; no mathematical statement changes.

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

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConcreteIntegralProjectionCone | D6 | Identical morphism and inferred type. |

ConcreteProjectionFieldDescent imports the item but does not mention targetUnit.

## Status

landed 20261025T201631-L-2591332 2026-10-25 (merge of deliver/D6/Sheaf.Paper.ConcreteIntegralProjectionCone)
