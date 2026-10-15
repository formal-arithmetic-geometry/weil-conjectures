# AlgebraicGeometry.ProEtale.exists_condensedQbar_refinement_of_local

## Reason

The statement uses finite free module objects, condensed coefficients, and ordinary
pullback. It does not use constructibility or local finite presentation. Replace the
broad constructibility import with the defining finite-free module import. The explicit
Basic import is redundant because UpperLowerStar.Defs publicly imports it. No declaration
signature, visibility, definition, or instance changes.

## Old

```lean
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
```

## New

```lean
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
```

## Users

`tools/downstream.py Sheaf.Paper.CondensedQbarLfpCoverComposition --uses
exists_condensedQbar_refinement_of_local` finds only CondensedQbarLfpLocalTriviality as
a user of the theorem. It is also the sole direct importer. It imports the composition
module privately, and publicly imports ConstructibleSheaf.ProEtaleModule.Def independently;
thus removing the re-export here changes neither its elaboration context nor its exports.
The following table includes all transitive module importers. No adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Unchanged theorem signature; its direct imports already provide the removed APIs. |
| Sheaf.Paper.CondensedStratumModelAssembly | XR1b27919aec52b018 | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| TargetsCheck | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Unaffected: the sole direct importer imports this module privately and retains its own public dependencies. |

## Status

landed 20261015T212907-L-2067624 2026-10-15 (merge of deliver/E1/Sheaf.Paper.CondensedQbarLfpCoverComposition)
