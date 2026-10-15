# Sheaf.AlgebraicGeometry.CondensedConstructibleSerre public imports

## Reason

The second reader found two unused public wrapper imports. The module uses source
`Scheme.Stratification` and internal `Mod`, rather than `Scheme.LocallyClosedStratification`
and `CategoryTheory.ringedSiteModules`. Remove those two direct imports. All four remaining
public imports are used by the unchanged theorem statements. This records the export change
required by the delivery preflight; no definition or theorem signature changes.

## Old

```lean
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
```

## New

```lean
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
```

## Users

Ran `tools/downstream.py Sheaf.AlgebraicGeometry.CondensedConstructibleSerre --uses
ringedSiteModules` and the corresponding `--uses LocallyClosedStratification` query.
The first found zero uses; the second found only the unused import in this item and the
explicit import in `CondensedFinitePresentationDescent`. The complete downstream list is
below, with holders read from `coord/claims/` on this machine at the second reading.
There are no adapted modules. No target statement or definition used by a target changes,
so no target-statement review is reopened. Both removed modules remain in the full import
closure via other dependencies.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | B3 | Already directly imports LocallyClosedStratification; no ringedSiteModules use. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | A4 | No declaration or statement changes; no removed-wrapper use. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | A3 | No declaration or statement changes; no removed-wrapper use. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | A2 | No declaration or statement changes; no removed-wrapper use. |
| `TargetsCheck` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No declaration or statement changes; no removed-wrapper use. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | B2 | No declaration or statement changes; no removed-wrapper use. |

## Status

landed 20261015T191321-L-1006542 2026-10-15 (merge of deliver/B3/Sheaf.AlgebraicGeometry.CondensedConstructibleSerre)
