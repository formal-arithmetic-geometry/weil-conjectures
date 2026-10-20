# AlgebraicGeometry.Scheme.Modules.coherentEtaleComparison_pullback imports

## Reason

Repair the current quarantined module recorded in `coord/rework.tsv`, restoring it
at its original path under `tools/rework.py`, rule 3. The current original fails
through `lcompile.py` in 0.8 seconds because upstream resolution comparison imports
collide with the Sheaf implementation exported by the canonical comparison:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv`.

After return `099ceb10b8`, construct the repair from the current quarantined source.
Remove only the two imports whose dependency closure loads the upstream duplicate;
preserve the other 15 private imports. The earlier returned packet removed all 17,
so this retry contains a narrower implementation change as well as fresh validation.
The repaired module compiles through `lcompile.py` in 2.3 seconds.

All public imports and all non-import text are unchanged. No definition, theorem
signature, proof, hole count or source-library file changes. No mathematical proof
or dependency pruning is claimed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## Users

A direct search of `lean/` and `quarantine/` finds the quarantined consumer below.
Its application at line 110 uses the exact unchanged signature. No consumer
adaptation is needed or included; its restoration belongs to its separate item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | E6 | Restored; conflicting private imports removed. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | separate quarantined rework item | Signature and public imports unchanged; no adaptation. |

The node `new-coherent-etale-comparison-pullback` already attaches the preserved
statement to its original path. Its attachment, statement and pending mathematical
proof dependencies remain unchanged. No target statement or definition changes.
The quarantine archive is preserved for the maintainer's reconciliation process.

## Status

landed 20261020T145503-L-2400871 2026-10-20 (merge of deliver/E6/Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback)
