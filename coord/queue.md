# Work queue

303 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (43 clusters, 1726 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.LevelwiseAdicTruncations` | 1 |  | error: Sheaf/Paper/LevelwiseAdicTruncations.lean:685:32: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | | Note: It is not pos |
| `Sheaf.Paper.ConstructibleCoefficientHomologyTriangulated` | 1 |  | error: Sheaf/Paper/ConstructibleCoefficientHomologyTriangulated.lean:61:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | Sh |
| `Sheaf.Paper.FinitePerfectAdicRealization` | 1 |  | error: Sheaf/Paper/FinitePerfectAdicRealization.lean:83:45: error(lean.unknownIdentifier): Unknown identifier `FinitePerfectModelsCompatible` | | Note: It is no |
| `Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules` | 1 |  | error: Sheaf/AlgebraicGeometry/CoefficientConstructibleEtaleModules.lean:111:10: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` |
| `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/Picard/CanonicalSinglePullbackComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, enviro |
| `Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation` | 1 |  | error: Sheaf/AlgebraicGeometry/StrictLocalMateContinuityPresentation.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension fail |
| `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons` | 1 |  | error: Sheaf/AlgebraicGeometry/RelativeMVResolvedRoofOpenMateComparisons.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/ResidueStalkHomologyMapComparison.lean:5:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackTensorUnitKFlat.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contai |
| `Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectOverlapStageEquivalence.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alre |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality f |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/QcoherentNormalizedPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturali |
| `Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal` | 1 |  | error: Sheaf/AlgebraicGeometry/TorAmplitudeOpenLocal.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'Algeb |
| `Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel` | 1 |  | error: Sheaf/AlgebraicGeometry/LocalKFlatPullbackModel.lean:5:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment already con |
| `Sheaf.TraceFormula.TwoTermPerfectDeterminant` | 1 |  | error: Sheaf/TraceFormula/TwoTermPerfectDeterminant.lean:112:17: error(lean.unknownIdentifier): Unknown identifier `derivedPullback` | | Note: A public declarat |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackTensorQCoh.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment already c |
| `Sheaf.CategoryTheory.GoodTruncationTotalDecalage` | 1 |  | error: Sheaf/CategoryTheory/GoodTruncationTotalDecalage.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'CategoryTh |
| `Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/BottomFreeChainDerivedSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alread |
| `Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/FiniteFreeResidueModelPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alre |
| `Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks` | 1 |  | error: Sheaf/AlgebraicGeometry/UniversalLowestFiberRanks.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'A |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectLowestMatrixCharts.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already contains 'A |
| `Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/AffinePerfectResidueModelNaturality.lean:84:19: error(lean.unknownIdentifier): Unknown constant `AlgebraicGeometry.Scheme.Modules |
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | 1 |  | error: Sheaf/Algebra/Homology/FilteredTensorGradedComparison.lean:6:0: error: import Sheaf.CategoryTheory.Filtration failed, environment already contains 'Categ |
| `Sheaf.Algebra.Homology.CanonicalTruncationFiltration` | 1 |  | error: Sheaf/Algebra/Homology/CanonicalTruncationFiltration.lean:68:4: error(lean.unknownIdentifier): Unknown constant `CategoryTheory.FilteredObject.HomPreserv |
| `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality` | 1 |  | error: Sheaf/AlgebraicGeometry/StalkComparisonPullbackNaturality.lean:5:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment already con |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase` | 1 |  | error: Sheaf/Algebra/Homology/AffineTildeTensorSourceComparisonCorePreBase.lean:6:0: error: import Sheaf.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws` | 1 |  | error: Sheaf/CategoryTheory/DerivedCategory/TraceFormalLaws.lean:67:2: error(lean.unknownIdentifier): Unknown constant `ModuleCat.extendScalars_additive_sheaf`  |
| `Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons` | 1 |  | error: Sheaf/AlgebraicGeometry/AffineModelCoherentObjectComparisons.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environmen |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean:26:23: error(lean.unknownIdentifier): Unknown identifier `Field` | | Note: A public declaration `Fi |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback` | 1 |  | error: Sheaf/AlgebraicGeometry/CoherentFrobeniusPullback.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality faile |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel` | 1 |  | error: Sheaf/AlgebraicGeometry/PerfectUniversalH0BottomModel.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alrea |
| `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` | 1 |  | error: Sheaf/CategoryTheory/FilteredHomotopySpectralSequence.lean:6:0: error: import WeilConjectures.CategoryTheory.CanonicalFiltration failed, environment alre |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 1 |  | error: Sheaf/AlgebraicGeometry/BottomChainModelPullbackTransport.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedProjectionMateOpenRestrictionComparison.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed,  |
| `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology` | 1 |  | error: Sheaf/AlgebraicGeometry/DerivedPullbackSingleCohomology.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit` | 1 |  | error: Sheaf/AlgebraicGeometry/FlatTelescopePullbackSumColimit.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alr |
| `Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel` | 1 |  | error: Sheaf/AlgebraicGeometry/HigherDirectImageDerivedModel.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment alrea |
| `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas` | 1 |  | error: Sheaf/AlgebraicGeometry/RawModuleScalarPullbackFormulas.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors faile |
| `Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` | 1 |  | error: Sheaf/AlgebraicGeometry/RingedSpaceDerivedAdjunctionGeneral.lean:70:18: error(lean.unknownIdentifier): Unknown constant `SheafOfModules.changeOfRings` |  |
| `Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` | 1 |  | error: Sheaf/AlgebraicGeometry/ScalarAbelianPullbackSquare.lean:6:0: error: import WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization failed, envir |
| `Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore` | 1 |  | error: Sheaf/AlgebraicGeometry/SmoothProperTensorPerfectCaseCore.lean:1:0: error: import WeilConjectures.AlgebraicGeometry.DerivedPullback failed, environment a |
| `Sheaf.Paper.ReconstructionUniformTower` | 1 |  | error: Sheaf/Paper/ReconstructionUniformTower.lean:82:14: error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification` | | Note: It is not po |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 27, stage 3 31 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (175)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 11 | 1 | repair | route |
| `Sheaf.Paper.SfHomTriangulated` | - | 1 | repair | route |
| `Sheaf.Paper.IntegralOperationsWellDefined` | - | 3 | repair | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | - | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` | - | 3 | proof | 1 |
| `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | - | 1 | proof | 1 |
| `Sheaf.CategoryTheory.InternalSectionTensorComparison` | - | 7 | proof | 1 |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | - | 6 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | - | 6 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | - | 6 | proof | 1 |
| `Sheaf.Paper.FiniteLevelProEtaleBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | - | 1 | proof | 1 |
| `Sheaf.Paper.LisseCompletedSystemComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.NormalizedDVREffectivity` | - | 1 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | - | 3 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | - | 1 | proof | 1 |
| `Sheaf.Paper.RingedProjectionRestriction` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PurityRelativeCone` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | - | 4 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 10 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` | - | 11 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSitePerfectDuality` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.AdicCoefficientDatum` | - | 5 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | - | 3 | proof | 2 |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedScalarShift` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | - | 24 | proof | 2 |
| `Sheaf.Paper.DeltaRestriction` | - | 4 | proof | 2 |
| `Sheaf.Paper.DualityPairing` | - | 2 | proof | 2 |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | - | 4 | proof | 2 |
| `Sheaf.Paper.IntegralHomReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.KoszulReconstruction` | - | 1 | proof | 2 |
| `Sheaf.Paper.OpenImmersionTensorPiece` | - | 1 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 10 | proof | 2 |
| `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality` | - | 3 | proof | 2 |
| `Sheaf.Paper.ProperOpenTowerComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | - | 3 | proof | 2 |
| `Sheaf.Paper.PurityNormalCone` | - | 4 | proof | 2 |
| `Sheaf.Paper.RefinementExchangeCoherence` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedPushforwardCompletion` | - | 1 | proof | 2 |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | - | 1 | proof | 2 |
| `Sheaf.Paper.StratumAmbientHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | - | 2 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 10 | proof | 2 |
| `Sheaf.Paper.WitnessCompatibility` | - | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.DirectImageScalarExchange` | - | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.BoundaryAlphaNormalization` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ClosedCostalkDuality` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.EtaleHomThickLocus` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.EtaleOpenTensor` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.OpenTensorNormalization` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.LisseAdicAutomorphismPullback` | 6 | 13 | proof | 3 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 11 | 3 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ShriekTensorComposition` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.RingedPresentationTransport` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | - | 6 | proof | 3 |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | - | 2 | proof | 3 |
| `Sheaf.Paper.BoundedBelowCtfReflection` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 4 | proof | 3 |
| `Sheaf.Paper.CoefficientHomZeroClass` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedAdicCoefficientDatum` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedKoszulQuotientComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackUnitTower` | - | 3 | proof | 3 |
| `Sheaf.Paper.ConstantTowerDirectImageNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.FibreFunctorBasepointTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteLevelRectangle` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteReductionConstructibility` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | - | 2 | proof | 3 |
| `Sheaf.Paper.InternalSliceDerivedHomComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | - | 2 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientProjectionCocycle` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedStrictTowerProjectionMorphism` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 7 | proof | 3 |
| `Sheaf.Paper.SupportedCup` | - | 4 | proof | 3 |
| `Sheaf.Paper.TorsionLimitSheafCompleteness` | - | 1 | proof | 3 |
| `Sheaf.Paper.UnboundedProperOpenInterchange` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 20 | proof | 3 |
| `Sheaf.SmoothPurity.InternalAdjunctionEvaluation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 7 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 7 | proof | 4 |
| `Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.AffineProjectiveComplexDerivedHom` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompactSupportSiteCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DivisibleExtensionDerivedReduction` | - | 5 | proof | 4 |
| `Sheaf.Paper.FiniteReductionReconstructionCompleted` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProperOpenCoefficientMate` | - | 1 | proof | 4 |
| `Sheaf.Paper.WContractibleConstantReductionsML` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RationalTermHomComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | - | 13 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | - | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | - | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 6 | proof | 5 |
| `Sheaf.Paper.CompletedConstantFiniteComplexRealization` | - | 1 | proof | 5 |
| `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` | - | 4 | proof | 5 |
| `Sheaf.Paper.GeoCartierExponentIndependence` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralLineTensorComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemNormalizedTensorClosure` | - | 2 | proof | 5 |
| `Sheaf.Paper.SystemTensorMateArrows` | - | 10 | proof | 5 |
| `Sheaf.SixFunctors.GeoCartierCoeffExtension` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CommutativeExchangeChart` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | - | 1 | proof | 6 |
| `Sheaf.Paper.ConstantTowerTransition` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.Paper.PullbackCoefficientIterateCoherence` | - | 2 | proof | 6 |
| `Sheaf.SixFunctors.CompletedTensorShiftRight` | - | 1 | proof | 6 |
| `Sheaf.Paper.KFlatMapFactorization` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.HigherDirectImagesLimits` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees` | - | 2 | proof | 11 |
| `Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction` | - | 1 | proof | 17 |
| `Sheaf.CategoryTheory.RingedSiteCechRefinementSquare` | - | 2 | proof | 17 |
| `Sheaf.Algebra.Homology.SplitCellComplexKFlat` | - | 1 | proof | 21 |

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
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
