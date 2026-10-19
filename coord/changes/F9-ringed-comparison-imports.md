# RingedComparisonTensorAdjunction public imports

## Reason

Prune unused high-level construction modules while retaining the smaller dependencies
required by the existing public declarations. All existing declaration signatures and
definition bodies remain identical. Only the re-exported imports change.

## Old

```lean
public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

## New

```lean
public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedKunnethFactorizations | R8 | Unchanged. Its lines 9 and 10 publicly import both removed dependencies directly. Its statements and definitions retain the same imports and meanings. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Unchanged. Imports the item only for proofs and imports RingedToposDerivedPushforwardComposition directly. No item declarations are used in its existing signatures or definition bodies. |

The current source search finds these two direct importers. RingedKunnethFactorizations
retains the removed exports through its own public imports. ArbitraryFieldAdjunctionScalars
imports this item only for proofs, so it does not re-export the removed imports; its
existing declarations do not use their interfaces. No consumer adaptation is required.

## Status

landed 20261019T034256-L-416496 2026-10-19 (merge of deliver/F9/Sheaf.Paper.RingedComparisonTensorAdjunction)
