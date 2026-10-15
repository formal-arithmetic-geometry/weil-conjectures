# WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal imports

## Reason

The module's declarations and the completed monoidality proof use no declaration
of `ModuleObjects.MapMod`. Remove its unused public import. Both direct users of
the item already import `MapMod` explicitly, so every transitive downstream user
continues to receive the same module-object interface through those imports.
There is no definition or declaration signature change and no target meaning
changes.

## Old

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
```

## New

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
```

## Users

`tools/downstream.py <item> --uses MapMod` finds exactly the three rows below;
the two downstream rows are also exactly the direct importers. Every one of
the 56 transitive downstream modules passes through one of those two direct
importers. No consumer source is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal | F3 | Unused import removed; complete proof compiles. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | F2 | Already publicly imports MapMod explicitly; no change. |
| WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def | unclaimed | Already publicly imports MapMod explicitly; no change. |

## Status

landed 20261015T154211-L-164497 2026-10-15 (merge of deliver/F3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal)
