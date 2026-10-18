# Sheaf.Algebra.Homology.KInjectiveProductsTermwise public imports

## Reason

Remove the unused public import of the empty compatibility module
`Sheaf.Algebra.Homology.KInjectiveProducts`, as required by stage-3 pruning.
The compatibility module has no declarations and publicly imports exactly the
three Mathlib modules already explicitly imported by the item. This is a textual
public-import removal with identical exported declarations. The proof-only imports
of the two KInjectiveBridge modules are also removed because the proof uses no
chosen resolution, and the three private imports used by the proof are added.

## Old

```lean
public import Sheaf.Algebra.Homology.KInjectiveProducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.KInjectiveBridge
import WeilConjectures.CategoryTheory.KInjectiveBridge
```

## New

```lean
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
```

The theorem signature and all definitions are unchanged. No target meaning changes
and no target statement review is reopened. No downstream source adaptation is
needed: the removed module has no declaration, and each of its three public imports
remains public here. The three direct importers are RingedCechKoszulDualLimit,
RingedStrictTowerHomotopyLimit, and LocalHomTowerCriterion; all import this item
privately. The table includes every transitive importer printed by
`tools/downstream.py Sheaf.Algebra.Homology.KInjectiveProductsTermwise --uses
termwise_product_isKInjective_and_isLimit`. That search found no downstream
mention of the theorem name. Each user's statement and definitions therefore keep
exactly their existing meaning and dependencies on public declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.RingedCechKoszulDualLimit | H1 | Unchanged; same public declarations remain available. |
| Sheaf.CategoryTheory.RingedKoszulCompletionReflector | unclaimed | Unchanged; same public declarations remain available. |
| Sheaf.CategoryTheory.RingedKoszulSystem | H2 | Unchanged; same public declarations remain available. |
| Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit | unclaimed | Unchanged; same public declarations remain available. |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison | S1 | Unchanged; same public declarations remain available. |
| Sheaf.Paper.AdicCompletionReduction | J3 | Unchanged; same public declarations remain available. |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | M1 | Unchanged; same public declarations remain available. |
| Sheaf.Paper.KoszulQuotientLimit | Y2 | Unchanged; same public declarations remain available. |
| Sheaf.Paper.LocalHomTowerCriterion | M4 | Unchanged; same public declarations remain available. |
| Sheaf.Paper.RestrictionLocalCompleteness | A2 | Unchanged; same public declarations remain available. |
| Sheaf.RingTheory.DerivedCompleteProductsTriangles | B2 | Unchanged; same public declarations remain available. |
| Sheaf.RingTheory.ModuleLocalizationTowerVanishing | H1 | Unchanged; same public declarations remain available. |
| Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete | Q1 | Unchanged; same public declarations remain available. |
| Sheaf.RingTheory.RlimPerfectComplete | R1 | Unchanged; same public declarations remain available. |

## Status

landed 20261018T062845-L-668373 2026-10-18 (merge of deliver/P3/Sheaf.Algebra.Homology.KInjectiveProductsTermwise)
