# AlgebraicGeometry.Scheme.ProEt.affine_weaklyContractible_evaluation_colimits

## Reason

Second reading removed redundant direct imports. Four were public imports: preservation
of limits, abelian-group filtered colimits, locally bijective maps, and left exact
sheafification. They are already publicly exported by the retained imports. Three proof
imports (ExactFunctor, Constructions.Filtered, and LimitsOfProductsAndEqualizers) are
likewise transitively available. The original three proof-dependency imports are replaced
by exact evaluation and the new direct-sum proof, as detailed in the report.

The exported import closure is identical: ModuleCat.Sheaf.Colimits publicly imports
Presheaf.Sheafification, which publicly imports Presheaf.Limits (and hence
Preserves.Limits) and Sites.LocallyBijective. LocallyBijective publicly imports
LocallySurjective, which publicly imports LocallyInjective, which publicly imports
Sites.LeftExact. ProEtaleDerivedCategory publicly imports Sites.Proetale; the chain
through UniversallyOpen, FinitePresentation, QuasiSeparated, Topology.Sheaves.CommRingCat,
and Ring.FilteredColimits publicly supplies Grp.FilteredColimits.

All existing declaration signatures remain byte-for-byte identical. No definition changes,
no target meaning changes, and no target statement review is reopened. This record makes
explicit the public-import cleanup detected conservatively by the preflight.

## Old

Original import block (the existing theorem signature is unchanged):

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Paper.SiteSheafificationSectionsLocal
```

## New

Delivered import block:

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
--uses affine_weaklyContractible_evaluation_colimits` lists the following downstream
modules. Only ProEtaleModuleCohomologyCoproducts mentions the theorem directly (six uses).
All retained public imports have the same transitive public closure as before, so every
user retains the same declarations and instances. No user is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CompletionMap | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | F4 | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.IntrinsicKoszulCompletion | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Same exported import closure and identical theorem type; no adaptation. |
| TargetsCheck | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same exported import closure and identical theorem type; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | Same exported import closure and identical theorem type; no adaptation. |

## Status

landed 20261015T183130-L-811621 2026-10-15 (merge of deliver/E1/Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits)
