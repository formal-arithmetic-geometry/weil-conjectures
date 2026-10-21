# Work queue

129 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (30 clusters, 1506 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.Paper.PbcRationalTransport` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.CategoryTheory.CartanEilenbergDecalageTruncationDiagram` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectLowestRankBoundOpen` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.DerivedCanonicalFiltration` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: reverted by the merge queue after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 27, stage 3 23 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (74)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 11 | 1 | repair | route |
| `Sheaf.Paper.LisseAdicAutomorphismPullback` | 6 | 1 | disputed | 3 |
| `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | - | 6 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | - | 4 | proof | 1 |
| `Sheaf.Paper.FiniteLevelProEtaleBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | - | 3 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | - | 1 | proof | 1 |
| `Sheaf.Paper.RingedProjectionRestriction` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` | - | 11 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.AdicCoefficientDatum` | - | 5 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | proof | 2 |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedScalarShift` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | - | 20 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | - | 2 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | - | 2 | proof | 2 |
| `Sheaf.Paper.OpenImmersionTensorPiece` | - | 1 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 7 | proof | 2 |
| `Sheaf.Paper.ProperOpenTowerComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | - | 1 | proof | 2 |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 7 | proof | 2 |
| `Sheaf.SixFunctors.BoundaryAlphaNormalization` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ClosedCostalkDuality` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ShriekTensorComposition` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | - | 4 | proof | 3 |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 2 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackUnitTower` | - | 3 | proof | 3 |
| `Sheaf.Paper.ConstantTowerDirectImageNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | - | 7 | proof | 3 |
| `Sheaf.Paper.PointSectionsDerivedReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurTwistCoefficientTensor` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.WitnessCompatibility` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 12 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 3 | proof | 4 |
| `Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility` | - | 2 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompactSupportSiteCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DivisibleExtensionDerivedReduction` | - | 5 | proof | 4 |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 3 | proof | 4 |
| `Sheaf.Paper.ScalarTensorPullbackNormalization` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 4 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.Paper.CompletedConstantFiniteComplexRealization` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemTensorMateArrows` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | - | 1 | proof | 6 |
| `Sheaf.Paper.ConstantTowerTransition` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.PointReductionUnits` | - | 5 | proof | 6 |

## Stage 3: held for an open upstream PR (18)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` | bundle/sec-curve-estimates-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
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
