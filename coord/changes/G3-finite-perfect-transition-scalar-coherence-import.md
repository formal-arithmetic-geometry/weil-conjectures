# AlgebraicGeometry.Scheme.finitePerfectAdic_coordinate_transition_maps

## Reason

The statement and proof need the marked coordinates, but do not use the scalar
realization coherence interface. Remove its redundant public import. The statement,
binders, universes, visibility and attributes of the existing theorem are unchanged.
The new scalar-extension helper is a proof-only import of the item.

## Old

```lean
public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
public import Sheaf.Paper.FinitePerfectAdicScalarCoherence
```

## New

```lean
public import Sheaf.Paper.FinitePerfectAdicMarkedOrigin
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicCoordinateTransitionMaps | G3 | One public import removed; theorem signature unchanged. |
| Sheaf.Paper.FinitePerfectAdicCoordinateTransitions | Not recorded in the shared snapshot | Sole direct importer; already publicly imports ScalarCoherence itself. Original unchanged consumer compiled against this delivery in the same import-order run (7.0 seconds). |

No other existing module is adapted. No definition or target statement changes.

## Status

landed 20261028T034755-L-3543780 2026-10-28 (merge of deliver/G3/Sheaf.Paper.FinitePerfectAdicCoordinateTransitionMaps)
