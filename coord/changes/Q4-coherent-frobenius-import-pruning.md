# coherent_frobenius_comparison imports

## Reason

The proof uses two comparison squares, resolution naturality, coefficient transport,
and elementary scalar and tensor calculations. The former full Cech-plan import block
is unnecessary in this module. The declarations retain their original signature.
Only the three imports required by that signature remain public. The comparison-square
obligations retain the Cech construction in their own nodes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural
public import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.CategoryTheory.SiteCechComplex
import Mathlib.Topology.Sheaves.Functors
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import Sheaf.Paper.CechComparisonMapNaturality
import Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientFactor
import Sheaf.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.DeltaFunctor
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.CoherentPowerComparison
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback
import Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison` reports zero
Lean importers. Its DAG parent still needs its statement, so the item is retained.
No consumer is adapted and no target statement changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | Q4 | Proof dependencies reduced; statement unchanged. |

## Status

landed 20261018T071213-L-1674975 2026-10-18 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison)
