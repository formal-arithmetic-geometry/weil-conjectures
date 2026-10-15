# condensedFiniteCoefficientCalculus

## Reason

Remove three public imports that neither the statements nor the completed proofs need.
This prunes the old sheaf-module proof route. The item now constructs finite freeness
with source internal module objects, uses the existing exact scalar-change API, and
proves the canonical coherence laws directly. No target, existing declaration signature,
coefficient definition, or public declaration visibility changes.

The static checker also reports the new generic-helper namespaces, opens, universe
names, and local attributes as commands. All added helpers are private, and the
irreducibility attributes are local. These commands only support the proofs.

## Old

```lean
public import Sheaf.Paper.CondensedCoefficientComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
```

## New

```lean
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
```

The signatures of `condensedFiniteCoefficientCalculus`, `condensedAlgClCoefficientCalculus`,
`condensedCoefficientCoherence`, and `condensedCoefficientTensorColimit` are unchanged.
Other new imports are proof-only. The removed proof-only imports are enumerated in the report.

## Users

`tools/downstream.py Sheaf.Paper.CondensedFlatCoefficientCalculus --names` lists the
following six downstream modules. Only the exchange-equality module imports the item
directly, using a proof-only import. Its public dependencies independently provide the
symbols in its signature. The transitive public interfaces therefore stay unchanged.
No adaptation of any module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Transitive importer through the unchanged exchange-equality module; no declaration signature changes. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Direct proof-only importer; its source is unchanged and is compiled against the new module. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Transitive importer through the unchanged exchange-equality module; no declaration signature changes. |
| TargetsCheck | unclaimed | Transitive importer through the unchanged exchange-equality module; no declaration signature changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer through the unchanged exchange-equality module; no declaration signature changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive importer through the unchanged exchange-equality module; no declaration signature changes. |

## Status

landed 20261015T185002-L-881934 2026-10-15 (merge of deliver/A4/Sheaf.Paper.CondensedFlatCoefficientCalculus)
