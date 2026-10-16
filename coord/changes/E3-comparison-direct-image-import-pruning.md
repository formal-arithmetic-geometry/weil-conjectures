# Sheaf.AlgebraicGeometry.ComparisonDirectImage public imports

## Reason

The proved comparison laws require only the two retained public source-library imports.
The removed public import exports no declaration used by this module's signatures or proofs.
The sole direct importer compiles unchanged with the reduced interface. The mathematical
statements and both public definitions are unchanged, so no target semantics are reopened.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
```

## Users

The downstream listing is for the module, since an import has no declaration name.
Only `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` imports the item directly;
its source was tested without adaptation. All other listed users are transitive.
No consumer module is changed in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientExchangeFromComparisons | C3 | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | E1 | Direct importer; original source compiled unchanged against pruned interface (11.6 s). |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| TargetsCheck | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive importer through the checked direct importer; no signatures or definitions changed. |

## Status

landed 20261016T102627-L-2294745 2026-10-16 (merge of deliver/E3/Sheaf.AlgebraicGeometry.ComparisonDirectImage)
