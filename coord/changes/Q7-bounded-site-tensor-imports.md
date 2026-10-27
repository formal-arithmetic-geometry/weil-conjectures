# Sheaf.Paper.BoundedSiteTensorTransposes imports

## Reason

The proved projection square and defining bounded Hom-chain calculation suffice.
Remove unused public proof-dependency imports so the item no longer exposes the
unrelated general comparison systems. Keep public imports needed by existing
signatures and arrow definitions; new proof imports are private. No declaration
signature or definition body changes. No source-library module changes.

## Old

```lean
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
import all Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
```

## New

```lean
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import all Sheaf.Paper.BoundedSiteAdjunctionTranspose
import all Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import Sheaf.Paper.SiteTensorUnitEvaluation
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
```

## Users

`tools/downstream.py Sheaf.Paper.BoundedSiteTensorTransposes --uses
boundedSiteTensorTransposes` reports zero downstream modules and only this module
as a named user. A separate repository import search also found no direct importer.
DAG parents with unfinished proofs remain unchanged, and the item is retained.
No target statement or the definitions it uses is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundedSiteTensorTransposes | Q7 | Prove the two holes and remove unused imports; preserve every existing declaration. |

## Status

landed 20261025T205542-L-3287101 2026-10-25 (merge of deliver/Q7/Sheaf.Paper.BoundedSiteTensorTransposes)
