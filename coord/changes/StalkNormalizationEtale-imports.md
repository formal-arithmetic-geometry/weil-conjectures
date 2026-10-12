# Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale imports

## Reason

Prune the unused fundamental-group functoriality theory. The signatures use only
Scheme.FiniteEtale. The original statements and definitions are unchanged.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | It imports the item non-publicly and uses its stalk-normalization theorem only. It already imports Functoriality itself, so its available declarations, definitions and statements are unchanged. No adaptation. |

## Status

landed 20261012T205628-L-931505 2026-10-12 (merge of deliver/E2/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale)
