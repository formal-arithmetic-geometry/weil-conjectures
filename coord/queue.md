# Work queue

92 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (13 clusters, 1358 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 27, stage 3 354 items.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


Not open yet: 302 nodes that below a finished node, not needed, 84 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (69)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 10 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 10 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | 1 | 2 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` | 2 | 10 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 4 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.Paper.DerivedNakayamaResolution` | 5 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 5 | proof | route |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SingleProperOpenFiniteNormalization` | 8 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.StrictTowerAlphaEvaluation` | 9 | 1 | proof | route |
| `Sheaf.Paper.CompletionMateComparison` | 9 | 21 | proof | route |
| `Sheaf.Paper.FiniteComparisonPresentation` | 9 | 1 | proof | route |
| `Sheaf.Paper.PurTwistIntegralLocalModels` | 9 | 1 | proof | route |
| `Sheaf.Paper.PurTwistRootLocalModels` | 9 | 1 | proof | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `Sheaf.Paper.AdicCompleteResidueConservative` | 10 | 1 | proof | route |
| `Sheaf.Paper.AdicPerfectReductionHomML` | 10 | 1 | proof | route |
| `Sheaf.Paper.AdicResidueFiniteLocalModels` | 10 | 1 | proof | route |
| `Sheaf.Paper.ActualCompletedReductionReconstruction` | 11 | 1 | proof | route |
| `Sheaf.Paper.AdicCompleteReductionCone` | 11 | 1 | proof | route |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | 11 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | 11 | 3 | proof | route |
| `Sheaf.Paper.IntegralCohomologyTorsionNormalForm` | 11 | 1 | proof | route |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 2 | proof | 1 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 1 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 4 | 15 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 7 | 11 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | 8 | 7 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | 9 | 14 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 4 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 7 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 4 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedProjectionCoherence` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 8 | 3 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | 9 | 4 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages` | - | 1 | proof | 14 |

## Stage 3: waiting for statements of dependencies (10)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SixFunctors.IntegralRestrictionLine` | 6 | 1 | `det-prop-diagonal-tower-coefficients` |
| `Sheaf.Targets.AffineSpaceRationalLine` | 8 | 1 | `det-prop-p1-adjunction-rational-triangle` |
| `Sheaf.Paper.DlConstructibleFibresExact` | - | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 8 | `lem-pur-system-level-projection-formula-coherence` |
| `Sheaf.Paper.FiniteTorStability` | - | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `sk-thm-sf-tensor-hom` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | - | 8 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SixFunctors.RationalOperations` | - | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SmoothPurity.NormalizedWitness` | - | 1 | `lem-pur-condensed-exceptional-reconstruction` |

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
