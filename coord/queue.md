# Work queue

90 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (52 clusters, 1733 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.LevelwiseAdicTruncations` | 1 |  | error: Sheaf/Paper/LevelwiseAdicTruncations.lean:685:32: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | | Note: It is not pos |
| `Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated` | 1 |  | error: Sheaf/Paper/ConstructibleCoefficientHomologyTriangulated.lean:61:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | Sh |
| `Sheaf.Paper.FinitePerfectAdicRealization` | 1 |  | error: Sheaf/Paper/FinitePerfectAdicRealization.lean:83:45: error(lean.unknownIdentifier): Unknown identifier `FinitePerfectModelsCompatible` | | Note: It is no |
| `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` | 1 |  | error: Sheaf/AlgebraicGeometry/CoefficientConstructibleEtaleModules.lean:111:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/Picard/CanonicalSinglePullbackComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, enviro |
| `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativeMVResolvedRoofOpenMateComparisons.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/ResidueStalkHomologyMapComparison.lean:5:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackTensorUnitKFlat.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contai |
| `Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectOverlapStageEquivalence.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alre |
| `Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal` | 1 |  | error: Sheaf/AlgebraicGeometry/TorAmplitudeOpenLocal.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'Algeb |
| `Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel` | 1 |  | error: Sheaf/AlgebraicGeometry/LocalKFlatPullbackModel.lean:5:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment already con |
| `Sheaf.TraceFormula.TwoTermPerfectDeterminant` | 1 |  | error: Sheaf/TraceFormula/TwoTermPerfectDeterminant.lean:112:17: error(lean.unknownIdentifier): Unknown identifier `derivedPullback` | | Note: A public declarat |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackTensorQCoh.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment already c |
| `Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/BottomFreeChainDerivedSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alread |
| `Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/FiniteFreeResidueModelPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alre |
| `Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks` | 1 |  | error: Sheaf/AlgebraicGeometry/UniversalLowestFiberRanks.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'A |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectLowestMatrixCharts.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'A |
| `Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/AffinePerfectResidueModelNaturality.lean:84:19: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Modules |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectUniversalH0BottomModel.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alrea |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 1 |  | error: Sheaf/AlgebraicGeometry/BottomChainModelPullbackTransport.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | 1 |  | error: Sheaf/Algebra/Homology/FilteredTensorGradedComparison.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'Categ |
| `Sheaf.Algebra.Homology.CanonicalTruncationFiltration` | 1 |  | error: Sheaf/Algebra/Homology/CanonicalTruncationFiltration.lean:68:4: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.FilteredObject.HomPreserv |
| `Sheaf.Paper.EtaleCERowCyclesNaturality` | 1 |  | error: Sheaf/Paper/EtaleCERowCyclesNaturality.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTheory.Decre |
| `Sheaf.Algebra.Homology.FilteredPageLocalization` | 1 |  | error: Sheaf/Algebra/Homology/FilteredPageLocalization.lean:179:11: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.FilteredObject.HomPreserving |
| `Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization` | 1 |  | error: Sheaf/AlgebraicGeometry/NewBaseOpenMateFactorization.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains |
| `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkComparisonPullbackNaturality.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already con |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildeTensorSourceComparisonCorePreBase.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws` | 1 |  | error: Sheaf/CategoryTheory/DerivedCategory/TraceFormalLaws.lean:67:2: error(lean.unknownIdentifier): Unknown constant `ModuleCat.extendScalars_additive_sheaf`  |
| `Sheaf.Paper.TowerPreservation` | 1 |  | error: Sheaf/Paper/TowerPreservation.lean:65:8: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | Compiled in 2.3 s |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalDerivedExchangeLeray.lean:6:0: error: import Sheaf.AlgebraicGeometry.StrictHenselization failed, environment already c |
| `Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration` | 1 |  | error: Sheaf/Algebra/Homology/FirstQuadrantVerticalConeFiltration.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains ' |
| `Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineModelCoherentObjectComparisons.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environmen |
| `Sheaf.AlgebraicGeometry.RelativeDualizingPair` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativeDualizingPair.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment already conta |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts` | 1 |  | error: Sheaf/AlgebraicGeometry/FlatComparisonPreservesCountableCoproducts.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, envi |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectHomOpenRestrictedMaps.lean:1:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativelyFlatDerivedBaseChange.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel` | 1 |  | error: Sheaf/AlgebraicGeometry/Morphisms/StrictHenselRootFiniteEtaleModel.lean:169:18: error(lean.unknownIdentifier): Unknown identifier `strictHenselization_st |
| `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` | 1 |  | error: Sheaf/CategoryTheory/FilteredHomotopySpectralSequence.lean:6:0: error: import WeilConjectures.CategoryTheory.CanonicalFiltration failed, environment alre |
| `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` | 1 |  | error: Sheaf/Algebra/Homology/SingleComplexAffineBaseChange.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alread |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusComparison.lean:6:0: error: object file '/home/ubuntu/weil-conjectures-sheaf/local/build/RW/Sheaf/AlgebraicGeome |
| `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedProjectionMateOpenRestrictionComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed,  |
| `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackSingleCohomology.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit` | 1 |  | error: Sheaf/AlgebraicGeometry/FlatTelescopePullbackSumColimit.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageDerivedModel.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alrea |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/RectangleOrdinaryGeometricPullback.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already co |
| `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` | 1 |  | error: Sheaf/AlgebraicGeometry/RingedSpaceDerivedAdjunctionGeneral.lean:70:18: error(lean.unknownIdentifier): Unknown constant `SheafOfModules.changeOfRings` |  |
| `Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarAbelianPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization failed, envir |
| `Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore` | 1 |  | error: Sheaf/AlgebraicGeometry/SmoothProperTensorPerfectCaseCore.lean:1:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.Paper.FlatFilteredComplexComparison` | 1 |  | error: Sheaf/Paper/FlatFilteredComplexComparison.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTheory.De |
| `Sheaf.Paper.ReconstructionUniformTower` | 1 |  | error: Sheaf/Paper/ReconstructionUniformTower.lean:82:14: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | | Note: It is not po |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 32, stage 3 203 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (6)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 11 | 3 | proof | route |
| `Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.Sites.FpStalkRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.SitePointReconstructionSets` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized` | - | 1 | proof | 21 |

## Stage 3: held for an open upstream PR (19)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
