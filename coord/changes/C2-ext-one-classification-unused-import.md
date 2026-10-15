# CategoryTheory.ext_one_extension_classification

## Reason

Remove the unused public import of `Mathlib.Algebra.Homology.ExactSequence`.
The statement only needs `Ext.Map`, whose public dependencies already provide Ext,
short complexes, short exactness and exact-functor maps. The proof uses no
`ComposableArrows` or finite exact-sequence interface. All declaration signatures
and definitions are unchanged, including all targets.

## Old

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ExactSequence
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
```

The added imports of `TStructure.AbelianSubcategory` and `TStructure.TruncLTGE`
are proof imports only. The three new helpers are private, proved theorems.

## Users

`tools/downstream.py` reports these eleven transitive importers. The sole direct
importer is `Sheaf.Paper.CondensedFinitePresentationDescent`, which imports this
module for its proof and uses no declarations from `ExactSequence`. Its statement
and proof are unchanged; the import does not export this module to its users.
The unchanged direct importer is compiled against the delivered module as a check.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No declaration changes; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No declaration changes; no adaptation needed. |
| TargetsCheck | unclaimed | No declaration changes; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No declaration changes; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No declaration changes; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No declaration changes; no adaptation needed. |

## Status

landed 20261015T175451-L-658071 2026-10-15 (merge of deliver/C2/Sheaf.CategoryTheory.ExtOneExtensionClassification)
