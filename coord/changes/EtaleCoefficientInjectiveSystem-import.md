# EtaleCoefficientInjectiveSystem import

## Reason
The direct public import of Mathlib.CategoryTheory.Preadditive.Injective.Basic is redundant because the retained public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance already supplies it transitively. The embedding module is imported privately for the proof.

## Old
```lean
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
```

## New
The import is removed; `Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystemEmbedding` remains a private proof import.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystem | P3 | Existing signatures are unchanged; the retained public TopologicalInvariance import supplies the signature dependencies. |
| Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveCokernelSystem | unclaimed | Direct importer; its original source compiles cleanly against the delivered modules, with unchanged signatures and no adaptation. |

## Status
landed 20261012T220524-L-1394727 2026-10-12 (merge of deliver/P3/Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystem)
