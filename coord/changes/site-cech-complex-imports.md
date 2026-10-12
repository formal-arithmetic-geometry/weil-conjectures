# Sheaf.CategoryTheory.SiteCechComplex imports

## Reason

The second reading found public imports used only through narrower modules. The definitions
require abelian groups, not AB4*, AB5 or categorical product exactness. Elementwise
exactness is used only in proofs. ExactFunctor is already imported by the proof-only
HomologicalComplexAbelian module. No declaration signature or definition changes.

## Old

```lean
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Category.Grp.AB
```

## New

```lean
public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
```

## Users

All direct importers below are checked against the narrowed module in a scratch overlay.
Their statements and definitions are unchanged; no adaptation is required. The removed
AB axioms and exact-functor equivalences are not referenced in these sources. The
remaining public imports provide the generic exactness and short-exactness notions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AlternatingCechComputes | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison | K2 | No statement or definition change; local overlay compilation checked. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1 | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.ColimitSiteCechComplex | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.SiteCechMathlibComparison | M1 | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.SiteCechVanishingCriterion | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.SiteInjectiveCechAcyclic | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.SiteSesCechH1Surjective | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic | N1 | No statement or definition change; local overlay compilation checked. |
| Sheaf.Paper.EtaleStandardCoverCech | none | No statement or definition change; local overlay compilation checked. |
| Sheaf.Topology.FilteredInjectiveCechAcyclic | none | No statement or definition change; local overlay compilation checked. |

## Status

landed 20261012T030943-L-1317572 2026-10-12 (merge of deliver/P1/Sheaf.CategoryTheory.SiteCechComplex)
