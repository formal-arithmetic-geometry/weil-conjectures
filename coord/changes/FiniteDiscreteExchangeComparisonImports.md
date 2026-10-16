# FiniteDiscreteExchangeComparisonImports

## Reason

Remove the redundant public import of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` from the item.
The retained public import of pro-etale `MorphismDefs` publicly imports
`Derived.BoundedConstructible`, `Derived.LowerShriek`, `Derived.UpperLowerStar`,
`UpperLowerStar.Defs`, `ModuleObject.Basic`, and then `ContinuousMap`.
Thus the removed direct import changes no available declaration, instance, statement,
or definition for downstream modules. The remaining import edits add private proof
inputs or remove redundant private proof inputs. The delivery preflight requires
this record for any removed public import, including a redundant one.

## Old

```lean
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.Paper.ConstantInternalModuleSheafEquivalence
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.Paper.FiniteDiscreteExchangeRealization
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
```

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteDiscreteExchangeComparison --uses
finiteDiscreteExchange_comparison` lists these six transitive users. Only
`IntegralFiniteExchangeComparison` mentions the theorem directly. All theorem
signatures and the public import closure are unchanged. No user needs adaptation.
Claim status below is the local shared-repository snapshot at second reading.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement or definition changes; same public import closure. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Direct theorem application unchanged; same signature and public import closure. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement or definition changes; same public import closure. |
| TargetsCheck | maintainer | Target signatures unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement or definition changes; same public import closure. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; same public import closure. |

## Status

landed 20261016T011143-L-264282 2026-10-16 (merge of deliver/B3/Sheaf.Paper.FiniteDiscreteExchangeComparison)
