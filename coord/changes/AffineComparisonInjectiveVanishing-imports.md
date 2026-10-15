# AffineComparisonInjectiveVanishing public imports

## Reason

The existing theorem needs `Sheaf.H` publicly. Export its defining Mathlib module directly
instead of the unrelated site-covering predicate module. The proof uses the proved upstream
terminal-object finite-cover Čech criterion. Its existing finite-product instance is enabled
locally; no new instance or definition is declared for importers. Every existing declaration
signature and visibility remains unchanged, as does the theorem's docstring.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
```

The following existing instance is enabled only in this file:

```lean
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing --direct
--uses IsSiteForCoverings` finds one direct importer and no use of the removed module's
predicate through this theorem. That importer already imports `SiteCoveringAxioms` itself.
No statement or definition changes here, hence all transitive consumers retain their meaning.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | not adapted | Already imports SiteCoveringAxioms; unchanged original checked against the sandbox overlay. |

## Status

landed 20261015T224822-L-2950964 2026-10-15 (merge of deliver/V3/Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing)
