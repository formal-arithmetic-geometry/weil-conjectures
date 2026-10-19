# Work queue

998 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (4)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sfb-constructible-cocone-hom-inj` | - | sorry_here |
| `lem-sfb-constructible-cocone-hom-surj` | - | sorry_here |
| `lem-a1-lisse-sections-stalk-evaluation` | - | none |
| `lem-trf-hilbert-samuel-local-presentations` | - | none |

## Stage 2: nodes to state (28)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sf-datum` | 1 | state | 91 |
| `sk-d-six` | 1 | state | 42 |
| `sk-def-sp-trace` | 2 | state | 2 |
| `lem-coef-finite-exceptional` | 1 | state | 117 |
| `fix-cor-verdier-exchange` | 2 | state | 105 |
| `fix-lem-exchanges` | 1 | state | 87 |
| `fix-prop-projection-formula` | 1 | state | 71 |
| `lem-pur-vector-integration-site-comparison` | 1 | state | 36 |
| `lem-pur-adic-purity-scalar-naturality` | 1 | state | 33 |
| `det-sp-tower-gluing` | 1 | state | 15 |
| `sk-thm-sf-tensor-hom` | 1 | state | 4 |
| `det-prop-diagonal-tower-trace` | 1 | state | 3 |
| `lem-tw-lisse-rational-realization` | 1 | state | 3 |
| `fix-lem-tensor-adjunction` | 1 | state | 1 |
| `cor-coef-verdier-weil-equivariance` | 1 | state | 0 |
| `det-sp-p1-trace` | 1 | state | 0 |
| `det-sp-tower-p1-adjunction` | 1 | state | 0 |
| `lem-coef-rational-retract-evaluation` | 1 | state | 0 |
| `lem-pur-condensed-exceptional-reconstruction` | 1 | state | 0 |
| `lem-sf-constant-semilinear-generator-comparison` | 1 | state | 0 |
| `lem-sf-proper-open-tensor-compatibility` | 1 | state | 0 |
| `lem-sfb-constructible-cocone-obj` | 1 | state | 0 |
| `lem-wf-constant-twist-coefficient-comparison` | 1 | state | 0 |
| `lem-zl-proper-unit-condensed-realization` | 1 | state | 0 |
| `thm-pur-vector-bundle-thom` | 1 | state | 0 |
| `lem-coef-finite-adjunction-transition` | 2 | state | 0 |
| `lem-coef-finite-free-compact-composition` | 2 | state | 0 |
| `nt-target-poincare-isiso` | 2 | state | 0 |

Not open yet: 295 nodes that below a finished node, not needed, 3 nodes that wait for stage 1 (statement downstream not grounded), 123 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (966)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 6 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 7 | 1 | repair | route |
| `Sheaf.Paper.IntegralConstantModelHeart` | 8 | 1 | repair | route |
| `Sheaf.Paper.PurityDiagonalBaseChangeCompared` | 6 | 1 | repair | route |
| `Sheaf.Paper.SfHomTriangulated` | 7 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance` | 7 | 1 | repair | route |
| `Sheaf.RepresentationTheory.ProcyclicTwoTerm` | 10 | 1 | repair | route |
| `Sheaf.Paper.CompactSupportComparisonPullbackCoherence` | 5 | 1 | repair | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 4 | 1 | disputed | route |
| `Sheaf.Paper.ProjectionFormulaCompactified` | 5 | 3 | disputed | route |
| `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction` | 8 | 1 | disputed | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | 5 |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | 2 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` | 3 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` | 3 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | 3 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | proof | route |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 5 | proof | route |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 6 | proof | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 6 | proof | route |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | 3 | 4 | proof | route |
| `Sheaf.Paper.FiniteReductionConstructibility` | 3 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | 3 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReduction` | 3 | 1 | proof | route |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 4 | proof | route |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | 3 | 2 | proof | route |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 4 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | route |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | 3 | 1 | proof | route |
| `Sheaf.Targets.VectorBundlePurity` | 3 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` | 4 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus` | 4 | 6 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` | 4 | 11 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 4 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | 4 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 6 | proof | route |
| `Sheaf.Paper.CompletedConstantSheafReduction` | 4 | 2 | proof | route |
| `Sheaf.Paper.CompletedPullback` | 4 | 2 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 4 | 24 | proof | route |
| `Sheaf.Paper.IntegralProperBaseChange` | 4 | 1 | proof | route |
| `Sheaf.Paper.IntrinsicCompletionCompleted` | 4 | 2 | proof | route |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | 4 | 3 | proof | route |
| `Sheaf.Paper.ProperBaseChangeRational` | 4 | 6 | proof | route |
| `Sheaf.Paper.PurityNormalCone` | 4 | 4 | proof | route |
| `Sheaf.Paper.ResidueLissePerfectLift` | 4 | 2 | proof | route |
| `Sheaf.SixFunctors.SmoothDualityBaseChangeCompat` | 4 | 1 | proof | route |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | 4 | 1 | proof | route |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | 4 | 1 | proof | route |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | 5 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | 5 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource` | 5 | 1 | proof | route |
| `Sheaf.DeligneLaumon.SmoothAffineFrontierStratification` | 5 | 1 | proof | route |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | 5 | 1 | proof | route |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | 5 | 4 | proof | route |
| `Sheaf.Paper.CompactSupportDirectImageTriangulated` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportReductionTower` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompactificationCoherence` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompleteCompactSupportProetale` | 5 | 13 | proof | route |
| `Sheaf.Paper.CompletedAdicIntrinsicCompletion` | 5 | 5 | proof | route |
| `Sheaf.Paper.CondensedERealization` | 5 | 1 | proof | route |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | 5 | 2 | proof | route |
| `Sheaf.Paper.ConstantWeilStructure` | 5 | 3 | proof | route |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | 5 | 1 | proof | route |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | 5 | 3 | proof | route |
| `Sheaf.Paper.FiniteCoefficientHomChange` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteCompactSupportConstructibility` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteConstructibleHom` | 5 | 2 | proof | route |
| `Sheaf.Paper.FiniteExtensionProperBaseChange` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteLevelProEtaleBaseChange` | 5 | 1 | proof | route |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | 5 | 1 | proof | route |
| `Sheaf.Paper.IntegralModels` | 5 | 1 | proof | route |
| `Sheaf.Paper.IntegralModelsOperations` | 5 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | 5 | 1 | proof | route |
| `Sheaf.Paper.LocalFrobeniusTrace` | 5 | 5 | proof | route |
| `Sheaf.Paper.MixedWeightsStability` | 5 | 1 | proof | route |
| `Sheaf.Paper.NormalizedDVREffectivity` | 5 | 1 | proof | route |
| `Sheaf.Paper.PbcDescentFunctors` | 5 | 1 | proof | route |
| `Sheaf.Paper.PbcIdempotentCompleteTriangulation` | 5 | 1 | proof | route |
| `Sheaf.Paper.PointFibreEquivalence` | 5 | 1 | proof | route |
| `Sheaf.Paper.PurAdicReconstruction` | 5 | 1 | proof | route |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | 5 | 3 | proof | route |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | 5 | 1 | proof | route |
| `Sheaf.Paper.RationalRestrictionGlue` | 5 | 1 | proof | route |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | 5 | 16 | proof | route |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | 5 | 2 | proof | route |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | 5 | 10 | proof | route |
| `Sheaf.Paper.SiteTensorLocalModelComparison` | 5 | 1 | proof | route |
| `Sheaf.Paper.UnboundedProperOpenInterchange` | 5 | 1 | proof | route |
| `Sheaf.Paper.WitnessCompatibility` | 5 | 1 | proof | route |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | 5 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralVerdier` | 5 | 1 | proof | route |
| `Sheaf.SixFunctors.ScalarSixPullback` | 5 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne` | 5 | 1 | proof | route |
| `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` | 6 | 1 | proof | route |
| `Sheaf.Algebra.Homology.SitePerfectTorWindow` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperSupportGeometricStalkCore` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` | 6 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | 6 | 10 | proof | route |
| `Sheaf.DeligneLaumon.BertiniSections` | 6 | 1 | proof | route |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | 6 | 2 | proof | route |
| `Sheaf.Paper.BoundaryDualizingComposition` | 6 | 1 | proof | route |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | 6 | 1 | proof | route |
| `Sheaf.Paper.CartesianCoefficientTwists` | 6 | 5 | proof | route |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | 6 | 1 | proof | route |
| `Sheaf.Paper.CoefficientHeart` | 6 | 1 | proof | route |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportCoefficientChange` | 6 | 8 | proof | route |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompleteProetale` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | 6 | 1 | proof | route |
| `Sheaf.Paper.CompletedScalarShift` | 6 | 1 | proof | route |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | 6 | 1 | proof | route |
| `Sheaf.Paper.DeltaRestriction` | 6 | 4 | proof | route |
| `Sheaf.Paper.DirectImageTorAmplitude` | 6 | 1 | proof | route |
| `Sheaf.Paper.DualityPairing` | 6 | 2 | proof | route |
| `Sheaf.Paper.EtaleGeometricBiduality` | 6 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | 6 | 16 | proof | route |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 5 | proof | route |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralConstructibleCompactness` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralCtfTriangulated` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | 6 | 13 | proof | route |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 3 | proof | route |
| `Sheaf.Paper.IntegralProperDirectSums` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic` | 6 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | route |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | 6 | 1 | proof | route |
| `Sheaf.Paper.NilpotentReductionStep` | 6 | 1 | proof | route |
| `Sheaf.Paper.PointSectionsFiniteness` | 6 | 1 | proof | route |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | 6 | 3 | proof | route |
| `Sheaf.Paper.SbcCompletedOperations` | 6 | 15 | proof | route |
| `Sheaf.Paper.SfBidualityClass` | 6 | 1 | proof | route |
| `Sheaf.Paper.SfLocalizationAllStages` | 6 | 3 | proof | route |
| `Sheaf.Paper.SfScalarExtensionComposition` | 6 | 2 | proof | route |
| `Sheaf.Paper.StratumAmbientHom` | 6 | 2 | proof | route |
| `Sheaf.Paper.TwistPreservesFiniteness` | 6 | 1 | proof | route |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | 6 | 7 | proof | route |
| `Sheaf.SixFunctors.BoundaryAlphaNormalization` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | 6 | 5 | proof | route |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.FlatModelGeneration` | 6 | 3 | proof | route |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | 6 | 6 | proof | route |
| `Sheaf.SixFunctors.OpenTensorNormalization` | 6 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.BertiniSingularLocusDimension` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` | 7 | 7 | proof | route |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | 7 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars` | 7 | 4 | proof | route |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | 7 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.OpenComplementKnown` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange` | 7 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | 7 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` | 7 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportLongExact` | 7 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence` | 7 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison` | 7 | 1 | proof | route |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | 7 | 4 | proof | route |
| `Sheaf.Paper.AdicPurityObjects` | 7 | 3 | proof | route |
| `Sheaf.Paper.ClosedSupportConstructible` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 7 | 27 | proof | route |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | 7 | 1 | proof | route |
| `Sheaf.Paper.DeltaProperPushforward` | 7 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerLimit` | 7 | 6 | proof | route |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | 7 | 5 | proof | route |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeHomComparison` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteProperLocalizing` | 7 | 3 | proof | route |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | 7 | 2 | proof | route |
| `Sheaf.Paper.FrobeniusSquareExchange` | 7 | 7 | proof | route |
| `Sheaf.Paper.IntegralCanonicalTruncations` | 7 | 3 | proof | route |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralConstructibleHeart` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralConstructibleTriangulated` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralProperProjectionFormula` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralTensorProduct` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralTensorPullback` | 7 | 8 | proof | route |
| `Sheaf.Paper.IntegralTensorShriek` | 7 | 2 | proof | route |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | 7 | 8 | proof | route |
| `Sheaf.Paper.MateOpenRestriction` | 7 | 1 | proof | route |
| `Sheaf.Paper.PbcFiniteStageKaroubian` | 7 | 1 | proof | route |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | 7 | 1 | proof | route |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | 7 | 8 | proof | route |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | 7 | 1 | proof | route |
| `Sheaf.Paper.PurityDncComparisons` | 7 | 4 | proof | route |
| `Sheaf.Paper.PurityGysinStructure` | 7 | 1 | proof | route |
| `Sheaf.Paper.PurityRelativeKummer` | 7 | 1 | proof | route |
| `Sheaf.Paper.RingComplexCechBaseChange` | 7 | 1 | proof | route |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 7 | 7 | proof | route |
| `Sheaf.Paper.TraceBaseChangeFirst` | 7 | 3 | proof | route |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteCompactProetale` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.FiniteDualizing` | 7 | 9 | proof | route |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | 7 | 1 | proof | route |
| `Sheaf.SmoothPurity.InternalAdjunctionEvaluation` | 7 | 1 | proof | route |
| `Sheaf.SmoothPurity.TensorMateEtalePrecomp` | 7 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedSiteTorFlatModel` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport` | 8 | 1 | proof | route |
| `Sheaf.Paper.AdicTorFlatCohomology` | 8 | 2 | proof | route |
| `Sheaf.Paper.BoundedSiteAdjunctionTranspose` | 8 | 4 | proof | route |
| `Sheaf.Paper.BrownExceptionalAdjoint` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportExchangeTransport` | 8 | 1 | proof | route |
| `Sheaf.Paper.CompactSupportSiteCoherence` | 8 | 1 | proof | route |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | 8 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerSystem` | 8 | 1 | proof | route |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | 8 | 3 | proof | route |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | 8 | 3 | proof | route |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | 8 | 1 | proof | route |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | 8 | 8 | proof | route |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | 8 | 7 | proof | route |
| `Sheaf.Paper.IntegralHeartLocalModel` | 8 | 9 | proof | route |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralStratumExtBound` | 8 | 1 | proof | route |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 8 | 7 | proof | route |
| `Sheaf.Paper.ProperCompactCoincidence` | 8 | 1 | proof | route |
| `Sheaf.Paper.ProperHeartBoundLattice` | 8 | 1 | proof | route |
| `Sheaf.Paper.ProperHeartBoundReduction` | 8 | 1 | proof | route |
| `Sheaf.Paper.ProperOpenCoefficientRefinement` | 8 | 1 | proof | route |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | 8 | 1 | proof | route |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | 8 | 2 | proof | route |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | 8 | 2 | proof | route |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | 8 | 1 | proof | route |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | 8 | 4 | proof | route |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | 9 | 4 | proof | route |
| `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality` | 9 | 4 | proof | route |
| `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleLocalizationComparison` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.HigherDirectImagesLimits` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | 9 | 7 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportedProductQuotientModel` | 9 | 7 | proof | route |
| `Sheaf.Paper.BoundedBelowCtfReflection` | 9 | 1 | proof | route |
| `Sheaf.Paper.DivisibleExtensionDerivedReduction` | 9 | 5 | proof | route |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | 9 | 7 | proof | route |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | 9 | 6 | proof | route |
| `Sheaf.Paper.IntegralStratumHomFormula` | 9 | 2 | proof | route |
| `Sheaf.Paper.ProperHeartBoundTorsion` | 9 | 1 | proof | route |
| `Sheaf.Paper.UniformConstructibleExtRational` | 9 | 1 | proof | route |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | 9 | 7 | proof | route |
| `Sheaf.SixFunctors.FieldTensor` | 9 | 1 | proof | route |
| `Sheaf.SixFunctors.FlatModel` | 9 | 4 | proof | route |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | 10 | 5 | proof | route |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback` | 11 | 1 | proof | route |
| `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` | 11 | 4 | proof | route |
| `Sheaf.Paper.GeoCartierExponentIndependence` | 11 | 1 | proof | route |
| `Sheaf.Paper.IntegralDirectImageTower` | 11 | 1 | proof | route |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | 11 | 21 | proof | route |
| `Sheaf.Paper.SupportedCupFunctoriality` | 11 | 13 | proof | route |
| `Sheaf.RingTheory.NagataJTwoOfWeaklyEtale` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | 11 | 1 | proof | route |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | 12 | 3 | proof | route |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | 12 | 7 | proof | route |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | 12 | 4 | proof | route |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | 12 | 1 | proof | route |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | 12 | 5 | proof | route |
| `Sheaf.RingTheory.NagataOfWeaklyEtale` | 12 | 1 | proof | route |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | 12 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | 13 | 7 | proof | route |
| `Sheaf.Paper.SmoothPurityTowerInjectiveComponents` | 13 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` | 14 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity` | 14 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | 14 | 6 | proof | route |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | 14 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule` | 15 | 1 | proof | route |
| `Sheaf.Paper.ConstantTowerDirectImageNormalization` | 15 | 3 | proof | route |
| `Sheaf.Paper.ExternalRHomConePairing` | 15 | 1 | proof | route |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | 15 | 1 | proof | route |
| `Sheaf.Paper.DenseOpenPiOneSurjective` | - | 8 | proof | route |
| `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralLfpConstantModelComparison` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` | 4 | 8 | proof | 1 |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | 4 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.AdicSmoothBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficients` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CoefficientFrobenius` | 5 | 5 | proof | 1 |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | 5 | 9 | proof | 1 |
| `Sheaf.Paper.ConstructibleCompleteBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 5 | 12 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.EtaleWeilFundamentalRepresentation` | 5 | 8 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 5 | 11 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientPoint` | 5 | 9 | proof | 1 |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | 5 | 13 | proof | 1 |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.LisseCompletedSystemComparison` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.PbcRationalTransport` | 5 | 3 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.QbarProperBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.QcqsCompactSupportRealization` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.SfCommonStageDirectImage` | 5 | 3 | proof | 1 |
| `Sheaf.Paper.StratifiedLattice` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | 5 | 1 | proof | 1 |
| `Sheaf.SixFunctors.RationalVerdier` | 5 | 1 | proof | 1 |
| `Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds` | 6 | 1 | proof | 1 |
| `Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.CommonStageCalculus` | 6 | 8 | proof | 1 |
| `Sheaf.Paper.ConstructibleTruncations` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 21 | proof | 1 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | 6 | 4 | proof | 1 |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | 7 | 4 | proof | 1 |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | 7 | 7 | proof | 1 |
| `Sheaf.Paper.RationalStalkExact` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.WeilTensorProduct` | 7 | 10 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | - | 16 | proof | 1 |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | - | 4 | proof | 1 |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | - | 1 | proof | 1 |
| `Sheaf.Paper.DlConstantFieldCharts` | - | 1 | proof | 1 |
| `Sheaf.Paper.EtaleWeilSheafEquivalence` | - | 1 | proof | 1 |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | - | 1 | proof | 1 |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | - | 1 | proof | 1 |
| `Sheaf.Paper.MiddleExtensionHcZero` | - | 1 | proof | 1 |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | - | 10 | proof | 1 |
| `Sheaf.Paper.WeilFourierInversion` | - | 2 | proof | 1 |
| `Sheaf.Paper.WeilOpenImageDelta` | - | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | 3 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteRingSectionDeformation` | 3 | 11 | proof | 2 |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | 3 | 5 | proof | 2 |
| `Sheaf.Paper.AdicCoefficientDatum` | 4 | 5 | proof | 2 |
| `Sheaf.Paper.KoszulReconstruction` | 4 | 13 | proof | 2 |
| `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity` | 4 | 1 | proof | 2 |
| `Sheaf.Paper.PbcUniformCompleteTriangulated` | 4 | 1 | proof | 2 |
| `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality` | 4 | 3 | proof | 2 |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | 4 | 2 | proof | 2 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 2 |
| `Sheaf.Paper.WeilCompletedTensorReflector` | 4 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | 5 | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaResolution` | 5 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteProperBaseChange` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCriterionReductions` | 5 | 8 | proof | 2 |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | 5 | 4 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | 5 | 2 | proof | 2 |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | 5 | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | 5 | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | 6 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction` | 6 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.FixSiteOpenExchange` | 6 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | 6 | 4 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionTensorComparison` | 6 | 7 | proof | 2 |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | 6 | 7 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSitePerfectDuality` | 6 | 1 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.AdicPuritySourceReduction` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | 6 | 11 | proof | 2 |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 6 | 11 | proof | 2 |
| `Sheaf.Paper.CoefficientHeartClosure` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientHeartFiltration` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedExchangeCoherence` | 6 | 9 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackReduction` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackTriangles` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | 6 | 4 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 6 | 19 | proof | 2 |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.FiniteReductionComparisons` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.FiniteSmoothCanonicalInterfaces` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 6 | 35 | proof | 2 |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | 6 | 12 | proof | 2 |
| `Sheaf.Paper.IntegralHomReductionComparison` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | 6 | 13 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComposition` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.LisseAdicAutomorphismPullback` | 6 | 13 | proof | 2 |
| `Sheaf.Paper.OpenImmersionTensorPiece` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | 6 | 45 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | 6 | 14 | proof | 2 |
| `Sheaf.Paper.PreservationConstructible` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PurityAffineLineOrientation` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.PurityGeneralAdmissibility` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.PuritySourceTransports` | 6 | 10 | proof | 2 |
| `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.RefinementExchangeCoherence` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.SemilinearDerivedSections` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | 6 | 19 | proof | 2 |
| `Sheaf.Paper.SmoothPurityMap` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.VectorBundlePurity` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.WeilCompactSupportCohomology` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.WeilIndSheafCategory` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | 6 | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.DirectImageScalarExchange` | 6 | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | 6 | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.OpenScalarExchange` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.ClosedCostalkDuality` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.EtaleHomThickLocus` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.EtaleOpenTensor` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | 6 | 3 | proof | 2 |
| `Sheaf.SixFunctors.IntegralLisseReductionEquivalence` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange` | 6 | 1 | proof | 2 |
| `Sheaf.TraceFormula.PointTransportComposition` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | 7 | 3 | proof | 2 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | 7 | 9 | proof | 2 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | 7 | 2 | proof | 2 |
| `Sheaf.Paper.FieldWeilShriekShiftData` | 7 | 7 | proof | 2 |
| `Sheaf.Paper.FiniteReductionRootCharts` | 7 | 3 | proof | 2 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | 7 | 5 | proof | 2 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | 7 | 9 | proof | 2 |
| `Sheaf.Paper.PointSectionsDerivedReduction` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | 7 | 10 | proof | 2 |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | 7 | 3 | proof | 2 |
| `Sheaf.Paper.PurInverseImageTensorHom` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.StratifiedLatticeRank` | 7 | 1 | proof | 2 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | 7 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.AdicPurityTwistReduction` | 8 | 7 | proof | 2 |
| `Sheaf.Paper.AdicStratifiedPerfect` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.CommonStageWeilShriek` | 8 | 5 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | 8 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteReductionChartCalculus` | 8 | 3 | proof | 2 |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.PbcWeilCategory` | 8 | 7 | proof | 2 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.RingedDerivedSliceLocalization` | 8 | 1 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.AdicPurityFiniteTensor` | 9 | 4 | proof | 2 |
| `Sheaf.Paper.ExceptionalFiniteRealization` | 9 | 5 | proof | 2 |
| `Sheaf.Paper.PointFibreDerivedTensor` | 9 | 1 | proof | 2 |
| `Sheaf.Paper.AdicPurityRootComparisons` | 10 | 6 | proof | 2 |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | 10 | 1 | proof | 2 |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | 11 | 1 | proof | 2 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | 11 | 3 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath` | - | 3 | proof | 2 |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicSectionClosedSupport` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 33 | proof | 2 |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | - | 8 | proof | 2 |
| `Sheaf.Paper.CompletedTensorHomTranspose` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayama` | - | 1 | proof | 2 |
| `Sheaf.Paper.FibreFunctorBasepointTransport` | - | 1 | proof | 2 |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | - | 2 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.ProperOpenTowerComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.RationalDirectImageRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SmoothLisseIntegralLattice` | - | 1 | proof | 2 |
| `Sheaf.Paper.TraceCompactificationCohomology` | - | 1 | proof | 2 |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.CompositionProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | - | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance` | 4 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint` | 4 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | 4 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ShriekTensorComposition` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteTateSiteDescent` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleProjectionFormulaArrows` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.PurityConventions` | 4 | 11 | proof | 3 |
| `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.CompatibleFiniteDerivedTrivializations` | 5 | 1 | proof | 3 |
| `Sheaf.Paper.CompletedConstantFiniteComplexRealization` | 5 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.BertiniSmoothMember` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHeartGeneration` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.CompactSupportFiniteAction` | 6 | 5 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | 6 | 7 | proof | 3 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | 6 | 3 | proof | 3 |
| `Sheaf.Paper.TateTwistLocallyFree` | 6 | 1 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatFinitePresentationRetract` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | 7 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleLocalDualInterval` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleTwistedBidualTransport` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` | 7 | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition` | 7 | 3 | proof | 3 |
| `Sheaf.CategoryTheory.CompactSupportRoosCofinality` | 7 | 2 | proof | 3 |
| `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit` | 7 | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | 7 | 2 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | 7 | 7 | proof | 3 |
| `Sheaf.Paper.AmplificationProper` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.CoefTowerCoaugmentation` | 7 | 5 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.CompletedMapReduction` | 7 | 3 | proof | 3 |
| `Sheaf.Paper.CompletedProjectionCoherence` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | 7 | 6 | proof | 3 |
| `Sheaf.Paper.EtaleLocalMonodromyRealization` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteClosedShriek` | 7 | 8 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteEtaleDescent` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteLevelRectangle` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | 7 | 2 | proof | 3 |
| `Sheaf.Paper.IntegralTwistBaseChange` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | 7 | 10 | proof | 3 |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.RingedPushforwardCompletion` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.SemilinearDerivedCalculus` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | 7 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | 7 | 2 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | 7 | 6 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | 7 | 9 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHomZeroClass` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.ConnectedTateLineEndomorphisms` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.DerivedReductionResolutionIndependence` | 8 | 5 | proof | 3 |
| `Sheaf.Paper.FieldShriekLowerBound` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralHeartDualizable` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.SupportedCup` | 8 | 4 | proof | 3 |
| `Sheaf.Paper.SystemOperationExchangeRealization` | 8 | 20 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | 8 | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | 8 | 15 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.AdicResidueLissePerfectLift` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.FourierAdicArtinSchreier` | 9 | 3 | proof | 3 |
| `Sheaf.Paper.TorsionLimitSheafCompleteness` | 9 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | 9 | 2 | proof | 3 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | 11 | 1 | proof | 3 |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | 12 | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | 12 | 20 | proof | 3 |
| `Sheaf.Algebra.Homology.RationalTermHomComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence` | - | 5 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientBidualTriangles` | - | 5 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws` | - | 6 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompactSupportPerfectness` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackUnitTower` | - | 3 | proof | 3 |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompositeIntegrationCounit` | - | 6 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 9 | proof | 3 |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | - | 44 | proof | 3 |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 3 |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | - | 7 | proof | 3 |
| `Sheaf.Paper.InternalSliceDerivedHomComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.IteratedWeilCocycle` | - | 1 | proof | 3 |
| `Sheaf.Paper.NormalProEtaleMonodromy` | - | 1 | proof | 3 |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | - | 4 | proof | 3 |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | - | 14 | proof | 3 |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurLisseMorphismRigidity` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | - | 3 | proof | 3 |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientProjectionCocycle` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedRefinementCoefficientSquare` | - | 1 | proof | 3 |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | - | 13 | proof | 3 |
| `Sheaf.Paper.SfRationalLocalGlobalPowerTorsion` | - | 1 | proof | 3 |
| `Sheaf.Paper.SmoothPurityCompactProjectionBaseChange` | - | 1 | proof | 3 |
| `Sheaf.Paper.TensorTraceTranspose` | - | 1 | proof | 3 |
| `Sheaf.Paper.TraceTransposeBaseChange` | - | 1 | proof | 3 |
| `Sheaf.Paper.TrfDevissageGeneration` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | - | 3 | proof | 3 |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry` | 5 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality` | 5 | 1 | proof | 4 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | 5 | 1 | proof | 4 |
| `Sheaf.Paper.RingedProjectionTensorComposition` | 5 | 1 | proof | 4 |
| `Sheaf.SixFunctors.TensorProjectionAdjunct` | 5 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation` | 6 | 4 | proof | 4 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | 6 | 5 | proof | 4 |
| `Sheaf.FieldTheory.BertiniFieldExtension` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | 7 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleGenericDirectImageExchange` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleGenericStratumMate` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KummerAffineLine` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | 8 | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | 8 | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | 8 | 14 | proof | 4 |
| `Sheaf.CategoryTheory.RingedPresentationTransport` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.CompletedReductionSquare` | 8 | 3 | proof | 4 |
| `Sheaf.Paper.FiniteComparisonLocalizing` | 8 | 2 | proof | 4 |
| `Sheaf.Paper.KunnethDerivedTensorTEst` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.ProperOpenCoefficientMate` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.QuotientCornerFrobeniusStructures` | 8 | 32 | proof | 4 |
| `Sheaf.Paper.RingedStrictTowerProjectionMorphism` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.SystemNormalizedTensorClosure` | 8 | 2 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainCoefficientArrows` | 8 | 1 | proof | 4 |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | 8 | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleGenericHomTriangle` | 8 | 5 | proof | 4 |
| `Sheaf.SixFunctors.EtaleGenericPerfectHom` | 8 | 1 | proof | 4 |
| `Sheaf.TraceFormula.IntegralConeCounitRealization` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial` | 9 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle` | 9 | 5 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | 9 | 1 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | 9 | 4 | proof | 4 |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | 10 | 1 | proof | 4 |
| `Sheaf.Paper.PointReductionUnits` | 10 | 5 | proof | 4 |
| `Sheaf.Paper.WContractibleConstantReductionsML` | 10 | 1 | proof | 4 |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | 13 | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.StandardGroupSchemes` | - | 12 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.FieldTheory.AlgebraicSeparableSmooth` | - | 1 | proof | 4 |
| `Sheaf.Paper.AffineProjectiveComplexDerivedHom` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstructibleHomComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | - | 1 | proof | 4 |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | - | 3 | proof | 4 |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.GeometricStalkPerfect` | - | 4 | proof | 4 |
| `Sheaf.Paper.PointReductionUnitNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerBound` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerLevels` | - | 3 | proof | 4 |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | - | 4 | proof | 4 |
| `Sheaf.Paper.TwistFrobeniusScalar` | - | 10 | proof | 4 |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleInternalHomDevissage` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompactificationLocalizing` | 5 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula` | 6 | 1 | proof | 5 |
| `Sheaf.Paper.KFlatConeComparison` | 6 | 1 | proof | 5 |
| `Sheaf.Paper.TateInverseLimitBaseChange` | 6 | 12 | proof | 5 |
| `Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison` | 7 | 2 | proof | 5 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | 7 | 7 | proof | 5 |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | 7 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion` | 8 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison` | 8 | 1 | proof | 5 |
| `Sheaf.FieldTheory.GeometricIrreducibilityTranscendental` | 8 | 1 | proof | 5 |
| `Sheaf.Paper.FiniteReductionReconstructionCompleted` | 8 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientFlat` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | 9 | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees` | 9 | 2 | proof | 5 |
| `Sheaf.Paper.ConnectedConstantH0` | 9 | 3 | proof | 5 |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | 9 | 1 | proof | 5 |
| `Sheaf.Paper.PointDerivedHomEvaluation` | 9 | 1 | proof | 5 |
| `Sheaf.Paper.PointSectionsReconstruction` | 9 | 1 | proof | 5 |
| `Sheaf.RepresentationTheory.DvrGalois` | 9 | 1 | proof | 5 |
| `Sheaf.SixFunctors.EtaleHomComplexPullback` | 9 | 7 | proof | 5 |
| `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy` | - | 5 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | - | 2 | proof | 5 |
| `Sheaf.AlgebraicGeometry.LisseSplitHomFlatConstructible` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.FrameDualMate` | - | 1 | proof | 5 |
| `Sheaf.Paper.CoefficientRealizationTransport` | - | 8 | proof | 5 |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | - | 1 | proof | 5 |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | - | 1 | proof | 5 |
| `Sheaf.Paper.DirectImageCtfOpenTor` | - | 1 | proof | 5 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | - | 1 | proof | 5 |
| `Sheaf.Paper.LocalizedTopChern` | - | 9 | proof | 5 |
| `Sheaf.Paper.PointCompletedEvaluation` | - | 3 | proof | 5 |
| `Sheaf.Paper.PullbackCoefficientIterateCoherence` | - | 2 | proof | 5 |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemTensorMateArrows` | - | 10 | proof | 5 |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | - | 1 | proof | 5 |
| `Sheaf.Paper.VaryingRingGraphSummand` | - | 20 | proof | 5 |
| `Sheaf.Paper.VectorBundleThomClass` | - | 17 | proof | 5 |
| `Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange` | - | 1 | proof | 5 |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | - | 6 | proof | 5 |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | - | 4 | proof | 5 |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.OpenFactorCoherence` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | - | 2 | proof | 5 |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | 6 | 1 | proof | 6 |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | 6 | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 7 | 9 | proof | 6 |
| `Sheaf.Paper.PurityFrameClass` | 7 | 4 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap` | 8 | 2 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic` | 8 | 1 | proof | 6 |
| `Sheaf.Paper.InterchangeProperPasting` | 8 | 1 | proof | 6 |
| `Sheaf.FieldTheory.HenselianDVRTameSequence` | 10 | 1 | proof | 6 |
| `Sheaf.Paper.CompactFiberStalk` | 10 | 4 | proof | 6 |
| `Sheaf.Paper.ConstantTowerTransition` | 10 | 1 | proof | 6 |
| `Sheaf.Paper.PurityDivisorClass` | 10 | 2 | proof | 6 |
| `Sheaf.Paper.PurityFrameIndependence` | 11 | 1 | proof | 6 |
| `Sheaf.Paper.RelativeSupportBottomDescent` | 12 | 16 | proof | 6 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompleteFlagBundle` | - | 8 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization` | - | 3 | proof | 6 |
| `Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport` | - | 3 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProperOpenSiteTransport` | - | 2 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement` | - | 2 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | - | 1 | proof | 6 |
| `Sheaf.Paper.CartierClassAgreement` | - | 1 | proof | 6 |
| `Sheaf.Paper.ChernFlagFormula` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | - | 1 | proof | 6 |
| `Sheaf.Paper.FlagLocalComparison` | - | 9 | proof | 6 |
| `Sheaf.Paper.FlagPullbackInjective` | - | 1 | proof | 6 |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | - | 4 | proof | 6 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 6 |
| `Sheaf.Paper.KummerAdditivity` | - | 3 | proof | 6 |
| `Sheaf.Paper.KunHigherExchangeCoefficientCube` | - | 1 | proof | 6 |
| `Sheaf.Paper.LocalizedFlagProduct` | - | 11 | proof | 6 |
| `Sheaf.Paper.PfRefinementCompatibility` | - | 1 | proof | 6 |
| `Sheaf.Paper.ProjectiveBundleFormula` | - | 1 | proof | 6 |
| `Sheaf.Paper.PurityChernClasses` | - | 1 | proof | 6 |
| `Sheaf.Paper.PurityRegularSection` | - | 17 | proof | 6 |
| `Sheaf.Paper.RationalSliceCompletedEvaluation` | - | 8 | proof | 6 |
| `Sheaf.Paper.RationalThickEvaluation` | - | 4 | proof | 6 |
| `Sheaf.SecSmoothPurity.DerivedExchangeCube` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.CompletedTensorShiftRight` | - | 1 | proof | 6 |
| `Sheaf.Paper.PurityFramePrincipalBoundary` | 8 | 2 | proof | 7 |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic` | 9 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.ProEtaleVanishingDetection` | 9 | 3 | proof | 7 |
| `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns` | 11 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.PurityRelativeCone` | 11 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates` | 11 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor` | 12 | 2 | proof | 7 |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | 12 | 6 | proof | 7 |
| `Sheaf.RingTheory.LocalGeneratingTuples` | 12 | 1 | proof | 7 |
| `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge` | 13 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpace` | - | 3 | proof | 7 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` | - | 3 | proof | 7 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.CommutativeExchangeChart` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleRelationQuotient` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.FlatValuationLifting` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange` | - | 1 | proof | 7 |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | - | 1 | proof | 7 |
| `Sheaf.Paper.ProEtaleCompositionTowerNormalization` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | 9 | 13 | proof | 8 |
| `Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology` | 10 | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion` | 12 | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.SmoothPairRegularEquations` | 12 | 1 | proof | 8 |
| `Sheaf.CategoryTheory.BoundedInjectiveFibreDescent` | 12 | 5 | proof | 8 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | 12 | 1 | proof | 8 |
| `Sheaf.RingTheory.RelativeRegularEquationsBaseChange` | 12 | 1 | proof | 8 |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | 13 | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleCoordinateSupport` | 14 | 6 | proof | 8 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleRelationKernelPair` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.ProperEtaleRelationFiniteNeighbourhood` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent` | - | 1 | proof | 8 |
| `Sheaf.Paper.SupportedHomAdjunctionTranspose` | - | 1 | proof | 8 |
| `Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectSums` | 7 | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.TruncationHomotopyColimit` | 7 | 1 | proof | 9 |
| `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel` | 13 | 1 | proof | 9 |
| `Sheaf.RingTheory.QuasiRegularFlatQuotientBaseChange` | 13 | 1 | proof | 9 |
| `Sheaf.RingTheory.QuasiRegularNoetherianLocal` | 13 | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` | 15 | 21 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AffineEtaleRelationSeparatedQuasiFinite` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` | - | 4 | proof | 9 |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.FppfAffineRefinement` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.QuasiAffineBaseChange` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleChart` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence` | - | 1 | proof | 9 |
| `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover` | - | 1 | proof | 9 |
| `Sheaf.RingTheory.SemilocalSubmoduleBasis` | - | 1 | proof | 9 |
| `Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent` | - | 1 | proof | 9 |
| `Sheaf.Algebra.Homology.FilteredConeLocalization` | 14 | 1 | proof | 10 |
| `Sheaf.Algebra.Homology.FiniteFilteredLocalization` | 14 | 7 | proof | 10 |
| `Sheaf.CategoryTheory.EnoughStrictFilteredInjectives` | 14 | 1 | proof | 10 |
| `Sheaf.Paper.FiniteFilteredGradedExactness` | 14 | 5 | proof | 10 |
| `Sheaf.RingTheory.QuasiRegularPrefixQuotient` | 14 | 1 | proof | 10 |
| `Sheaf.Paper.KFlatMapFactorization` | 16 | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.EtaleAtlasPresentation` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.FppfFamilyAffineEffectivityReduction` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.FpqcInvariantIntersectionNeighbourhoods` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.IndQuasiAffinePermanence` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange` | - | 2 | proof | 10 |
| `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction` | - | 1 | proof | 10 |
| `Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding` | - | 1 | proof | 10 |
| `Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial` | - | 1 | proof | 10 |
| `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits` | 15 | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.IntersectionStructureSections` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality` | - | 1 | proof | 11 |
| `Sheaf.Paper.KunBaseChange` | - | 3 | proof | 11 |
| `Sheaf.RingTheory.QuasiFiniteComposition` | - | 1 | proof | 11 |
| `Sheaf.Targets.BaseChangeTowardsFields` | - | 1 | proof | 11 |
| `Sheaf.Topology.FilteredSpectrumTopologicalLimit` | - | 1 | proof | 11 |
| `Sheaf.AlgebraicGeometry.AbelianDegreeZeroFlatBaseChange` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.InvertibleOrdersColimit` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.KunnethBaseChangeFailure` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing` | - | 1 | proof | 12 |
| `Sheaf.RingTheory.FiniteTypeFppfSourceDescent` | - | 1 | proof | 12 |
| `Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange` | - | 2 | proof | 13 |
| `Sheaf.AlgebraicGeometry.OpenProductExchange` | - | 1 | proof | 13 |
| `Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders` | - | 1 | proof | 13 |
| `Sheaf.RingTheory.ColimOfLocalizations` | - | 1 | proof | 13 |
| `Sheaf.AlgebraicGeometry.AffineProjectiveCompactification` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.ClosedPointSupportDetection` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.ClosedPointsProduct` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.EtaleBaseChangeOpenClosed` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.StrictHenselizationLimit` | - | 1 | proof | 14 |
| `Sheaf.CategoryTheory.KunDescentLimit` | - | 1 | proof | 14 |
| `Sheaf.Paper.KunBcKunnethCompat` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.ClosedPointSupportGlobalGeneration` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.ClosedPointSupportVanishing` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.KunnethMapAgrees` | - | 2 | proof | 15 |
| `Sheaf.AlgebraicGeometry.SeparableClosureConservative` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis` | - | 1 | proof | 15 |
| `Sheaf.AlgebraicGeometry.ClosedPointSheafApproximation` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.GlobalGeneratedStalkwise` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.IntegralProperProjectionFormula` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.SepClosedEtaleGlobalGeneration` | - | 1 | proof | 16 |
| `Sheaf.CategoryTheory.GloballyGeneratedSheafColimit` | - | 1 | proof | 16 |
| `Sheaf.Algebra.Homology.IntegerFlatRepresentative` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.FiniteClosedPoints` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion` | - | 1 | proof | 17 |
| `Sheaf.RingTheory.Flat.LazardPresentation` | - | 1 | proof | 17 |
| `Sheaf.Algebra.Homology.IntegralBoundedKunnethExact` | - | 1 | proof | 18 |
| `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` | - | 1 | proof | 19 |
| `Sheaf.Algebra.Homology.DerivedCanonicalFiltration` | - | 1 | proof | 20 |
| `Sheaf.Algebra.Homology.FilteredPageLocalization` | - | 3 | proof | 20 |
| `Sheaf.Algebra.Homology.FilteredTensorGradedComparison` | - | 2 | proof | 20 |
| `Sheaf.Algebra.Homology.FilteredTensorLocalization` | - | 1 | proof | 20 |
| `Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement` | - | 1 | proof | 20 |
| `Sheaf.Algebra.Homology.BoundedDerivedRoofs` | - | 1 | proof | 21 |
| `Sheaf.Algebra.Homology.CanonicalTruncationFiltration` | - | 1 | proof | 21 |
| `Sheaf.Algebra.Homology.FilteredQuasiIsoFractions` | - | 1 | proof | 21 |
| `Sheaf.Algebra.Homology.SplitCellComplexKFlat` | - | 1 | proof | 21 |
| `Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized` | - | 1 | proof | 21 |

## Stage 3: waiting for statements of dependencies (32)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SmoothPurity.NormalizedWitness` | 1 | 1 | `lem-pur-condensed-exceptional-reconstruction` |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | 5 | 1 | `def-pur-affine-space-comparison` |
| `Sheaf.Paper.FiniteReductionOfPurity` | 5 | 8 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteTorStability` | 5 | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.SixFunctors.CoefQbarVerdier` | 5 | 1 | `lem-coef-rational-retract-evaluation` |
| `Sheaf.SixFunctors.RationalOperations` | 5 | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | 6 | 12 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | 6 | 1 | `fix-prop-projection-formula` |
| `Sheaf.Paper.DlConstructibleFibresExact` | 6 | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.DualizingObjectPurity` | 6 | 1 | `lem-pur-projection-purity-agreement` |
| `Sheaf.Paper.PurityCompositionCoherence` | 6 | 12 | `fix-prop-projection-formula` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | 6 | 8 | `lem-coef-finite-exceptional` |
| `Sheaf.SixFunctors.IntegralDualizing` | 6 | 1 | `lem-coef-finite-adjunction-transition` |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | 6 | 1 | `det-prop-diagonal-tower-coefficients` |
| `Sheaf.Paper.CohomologicalSmoothComposition` | 7 | 1 | `fix-prop-projection-formula` |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | 7 | 15 | `fix-lem-exchanges` |
| `Sheaf.Paper.SmoothPurityQbar` | 8 | 1 | `det-sp-integral-adjunction-bijection` |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | 8 | 1 | `fix-lem-exchanges` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | 10 | 4 | `det-sp-tower-gamma` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | 13 | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula` | - | 1 | `def-sf-pf` |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | - | 2 | `cor-coef-verdier-weil-equivariance` |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | - | 2 | `fix-prop-projection-formula` |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | - | 5 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | - | 5 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.FiniteProductCompactification` | - | 2 | `fix-lem-exchanges` |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | - | 1 | `lem-pur-vector-integration-site-comparison` |
| `Sheaf.Paper.FourierKernelConvolution` | - | 8 | `sk-thm-sf-package` |
| `Sheaf.Paper.RationalPurityPresentation` | - | 13 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `fix-lem-exchanges` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 8 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | - | 1 | `fix-prop-projection-formula` |

## Stage 3: held for an open upstream PR (21)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-six-functors-c1,bundle/sec-smooth-purity-d1 |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence` | bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
