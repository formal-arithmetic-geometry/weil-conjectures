# Work queue

505 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (22)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `thm-weil-pbc-weak-etale-strict-local` | 5 | none |
| `def-weil-pbc-ind-etale-algebra` | 6 | none |
| `lem-weil-pbc-ind-etale-stability` | 6 | none |
| `lem-weil-pbc-weak-etale-field` | 6 | none |
| `lem-weil-pbc-weak-etale-integral-closure` | 6 | none |
| `lem-weil-pbc-weak-etale-tor` | 7 | none |
| `prop-weil-pbc-strict-local-exchange` | 1003 | sorry_here |
| `lem-weil-pbc-horseshoe-correction` | 1007 | none |
| `lemma-weil-pbc-curve-normalization-constant` | 1008 | sorry_here |
| `lemma-weil-pbc-smooth-curve-artin-schreier` | 1008 | sorry_here |
| `lemma-weil-pbc-smooth-curve-kummer-localization` | 1008 | sorry_here |
| `lemma-weil-pbc-normalization-exact-sequence` | 1009 | sorry_here |
| `lem-weil-pbc-associated-graded-ring-structure` | 1019 | none |
| `lem-weil-pbc-thickening-system-pushforward-lifting-assembly` | 1022 | none |
| `lem-weil-pbc-free-complex-base-lift` | 1023 | none |
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |
| `sbc-prop-extension-by-zero-and-arbitrary-base-change` | - | none |
| `prop-nagata-relative-proj-functoriality` | - | none |
| `def-nagata-relative-proj` | - | none |
| `lemma-nagata-proj-chart-ring-cocycle` | - | none |
| `lemma-nagata-relative-proj-exists` | - | none |

## Stage 2: nodes to state (8)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-weil-cohomological-support` | 1 | state | 38 |
| `def-weil-pure-dimension` | 1 | state | 11 |
| `def-nagata-final-fp-envelope` | 4 | state | 5 |
| `lem-weil-unique-subfield-of-closure` | 1 | state | 57 |
| `lem-weil-geometrically-connected-algebraic-closure` | 1 | state | 11 |
| `cor-weil-pbc-geometric-fiber-finite` | 1 | state | 0 |
| `lem-weil-pbc-geometric-point-pullback-stalk` | 1 | state | 0 |
| `lemma-nagata-final-open-immersion` | 3 | state | 0 |

Not open yet: 238 nodes that wait for stage 1, 28 nodes that wait for a statement dependency.

## Stage 3: modules to prove (475)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 21 | 1 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 20 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 22 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
| `Sheaf.CategoryTheory.SiteSystemStrictificationData` | 10 | 1 | disputed |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` | 10 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `Sheaf.RingTheory.KoszulRegularSequenceDualComplex` | 14 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotient` | 17 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` | 18 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChowFiniteCohomologyWitness` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageSectionDenominators` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageSectionTorsion` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleTensorSections` | 8 | 2 | proof |
| `Sheaf.AlgebraicGeometry.CoherentGenericFilteredExtension` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportAdicChain` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageEventualZero` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IntegralIdealsCommonGenericLattice` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentCokernelRelationsLocal` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Cohomology.AbelianCechAugmentationBoundarySquares` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveScalarBaseChange` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechSectionBaseChange` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiTargetComparison` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericIdealStalkEmbeddingExtension` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LinearCechSheafResolution` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` | 10 | 4 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CechSheafConstruction` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CechSheafLocalQuasiIso` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Cohomology.OpenImmersionCoefficientUnit` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EpiOverFunctor` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteTypeKernelLocalGenerators` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectSectionsProjectiveModel` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineProjectiveSectionsSheafification` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitBinarySuccessorCoconeSegment` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate` | 12 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCoefficientInjectiveSystemEmbedding` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientLaws` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystem` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenComparisonCertificate` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FixedAbelianDescendedSectionLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassRestriction` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineCohomologySectionEquiv` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaceFixed` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionEventualEquality` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility` | 15 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison` | 15 | 1 | proof |
| `Sheaf.CategoryTheory.ExactFunctorResolutionCocycle` | 15 | 1 | proof |
| `Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds` | 15 | 1 | proof |
| `Sheaf.Paper.EtaleCESupportedFirstPageLifts` | 15 | 1 | proof |
| `Sheaf.RingTheory.PopescuParameterCoefficients` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceBase` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlternatingCechResolutionCore` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlternatingCechResolutionExchange` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverseBijective` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageCompletedComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexSingleNaturality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModulePullbackComparisonIsoTransport` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedResolutionEvaluation` | 16 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedFunctorValueTriangleCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePushoutModuleSectionPresentation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenFixedCounitsCompatibility` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitAnnihilators` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineTensorDictionary` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 17 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonRestriction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupUnitComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjGradedModuleChartBasisComparisonFixedMaps` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteFiniteSectionEventualZero` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteRawFiniteSectionsLift` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitStageKanCocone` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredStationaryCycleComparison` | 17 | 1 | proof |
| `Sheaf.RingTheory.BoundedFiniteFreeResolution` | 17 | 1 | proof |
| `Sheaf.RingTheory.Derivation.FiniteCoefficientPreparation` | 17 | 1 | proof |
| `Sheaf.RingTheory.PopescuSpecialChartInjective` | 17 | 1 | proof |
| `Sheaf.RingTheory.PopescuStandardReductionFactorCore` | 17 | 1 | proof |
| `Sheaf.RingTheory.WellOrderedUnionProjectivePresentation` | 17 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewise` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialComponent` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineModuleFiniteType` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleIdealKernelIso` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleTensorSectionsRightExact` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkIsoNeighborhood` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionAffineComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionPushforwardLimitIso` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GeometricGenericCoverModel` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftCompatibility` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardCupProductLocalCriterion` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapInjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapSurjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingChartCrossMultiplication` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons` | 18 | 2 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledAffineAlgebraization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteKanUnitRelations` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientPageMaps` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteCoconeStationary` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.SecondFiltrationRowGradedCycles` | 18 | 1 | proof |
| `Sheaf.Paper.AffinePerfectKoszulPrincipalUnit` | 18 | 1 | proof |
| `Sheaf.Paper.CohomologySectionDivision` | 18 | 1 | proof |
| `Sheaf.Paper.EtaleCEQuotientPageDescent` | 18 | 1 | proof |
| `Sheaf.Paper.EtaleCETotalizeAugmentedComparison` | 18 | 1 | proof |
| `Sheaf.Paper.ModuleCohomologyCupProduct` | 18 | 1 | proof |
| `Sheaf.RingTheory.AdjoinSingletonSplittingPolynomialCover` | 18 | 1 | proof |
| `Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange` | 18 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationModelStage` | 18 | 1 | proof |
| `Sheaf.RingTheory.FlatFinitePresentationModel` | 18 | 1 | proof |
| `Sheaf.RingTheory.KoszulComplementaryEquivalences` | 18 | 1 | proof |
| `Sheaf.RingTheory.PopescuPartialChartPolynomial` | 18 | 1 | proof |
| `Sheaf.RingTheory.PopescuZeroBaseSingleChartPresentation` | 18 | 1 | proof |
| `Sheaf.RingTheory.SyntomicEquationCountComparisonDimension` | 18 | 1 | proof |
| `Sheaf.RingTheory.TatePurelyInseparableClosureQuotientFinite` | 18 | 1 | proof |
| `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` | 18 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedFreeSurjection` | 19 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.AdicTowerFreeKernelCorrection` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.ChainConeCoordinatesIso` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.ConeHorizontalProjectionKernel` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorCurryNaturalPure` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorLocalizedExt` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenSupportedHomologyApproximation` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleDegreeExactTermHomQuasiIso` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.StupidTailHomShortExact` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.VerticalCutoffComparisonKernelTwoTerm` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePushoutRingSectionMapInjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePushoutRingSectionProducts` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AnnihilatorQuasicoherent` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AnnihilatorStalkLocalLift` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ArtinReesAffineComparison` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BasicOpenTildeScalarIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitQuotient` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotient` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineReconstructionObjectwise` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernelFactorization` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletionThickeningCokernelReflection` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineDerivationSpan` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineLiftInjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChangeAlgebra` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction` | 19 | 2 | proof |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenModuleImageAmalgamation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPerfectModelTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOfOpenPullbacks` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardFiberRankClopen` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrefixDeletionExistence` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrefixDeletionRestrictions` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalQuotientMultiplicationImage` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonExact` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientArithmetic` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkFiniteFree` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationDescentGluing` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningGluedAtlas` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonColumnStep` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedIso` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteAbelianPairwiseEventualMatching` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.SingleHomologyShiftComparison` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.TruncationCoupleNaturality` | 19 | 1 | proof |
| `Sheaf.Paper.BalancedActionDirectImageModule` | 19 | 1 | proof |
| `Sheaf.Paper.NoetherianApproximation` | 19 | 1 | proof |
| `Sheaf.Paper.ObjectCohomologyResolutionCocycleEquivalence` | 19 | 1 | proof |
| `Sheaf.RepresentationTheory.LocallyConstantCochainsStructure` | 19 | 1 | proof |
| `Sheaf.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence` | 19 | 1 | proof |
| `Sheaf.RingTheory.BoundedResolutionUnitEntryCancellation` | 19 | 1 | proof |
| `Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete` | 19 | 1 | proof |
| `Sheaf.RingTheory.LengthQuotSMulTopFractionFieldSubmodule` | 19 | 1 | proof |
| `Sheaf.RingTheory.PolynomialCoefficientConormalInclusion` | 19 | 1 | proof |
| `Sheaf.RingTheory.PolynomialLocalWeakRegularSequenceDescent` | 19 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesNormalDomain` | 19 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesParameterPerturbation` | 19 | 1 | proof |
| `Sheaf.RingTheory.ProjectiveSymmetricCoefficientIntersection` | 19 | 1 | proof |
| `Sheaf.RingTheory.RegularFiberKernelParameterLift` | 19 | 1 | proof |
| `Sheaf.RingTheory.SyntomicPresentationLocalKernel` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.FilteredFreeTelescopeSplitting` | 20 | 1 | proof |
| `Sheaf.Algebra.Homology.TensorHomologyMapBijective` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedComplexTensorProperSupportBound` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsMap` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenGluing` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteGaloisTensorCoproduct` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPrecomposePus` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalAssociatedGradedAlgebraExists` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelGradedActionExists` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelGradedActionLocalGenerators` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechStageKernel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechStageLifting` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NoetherianApproximationData` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NoetherianBoundedCoherentPseudoCoherent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyFinite` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectJumpLoci` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOfPseudoCoherentFiniteTorDimension` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectRelativeTensorLocallyBounded` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectTensorBoundedCoherent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectTensorFiniteRelativeTor` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupCochain` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechFiniteColumnModel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 11 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenSectionsResolutionQuasiIso` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperDirectImageFiniteTor` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` | 20 | 1 | proof |
| `Sheaf.FieldTheory.PIndependentInsert` | 20 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsCanonicalColimitCore` | 20 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsCanonicalTransformation` | 20 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 20 | 7 | proof |
| `Sheaf.Paper.SectionsOverQuasiCompactOpen` | 20 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientDescent` | 20 | 1 | proof |
| `Sheaf.RingTheory.FibreDimensionLocalizedBound` | 20 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationKerRangeCokernel` | 20 | 1 | proof |
| `Sheaf.RingTheory.FlatRegularFibreParameterSelection` | 20 | 1 | proof |
| `Sheaf.RingTheory.GeometricallyRegularH1Injective` | 20 | 1 | proof |
| `Sheaf.RingTheory.MinimalFreeModel` | 20 | 1 | proof |
| `Sheaf.RingTheory.PopescuQuotientBasisEnlargement` | 20 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesAdicEvaluation` | 20 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesCohenFormallySmoothAdic` | 20 | 2 | proof |
| `Sheaf.RingTheory.RegularSequenceFlatClosedFiber` | 20 | 1 | proof |
| `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPartialLocalFlat` | 20 | 1 | proof |
| `Sheaf.RingTheory.SimpleFiltration` | 20 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps` | 21 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModelAux` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` | 21 | 3 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomKFlat` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomScalarExtension` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineCoverModuleEmbedding` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectPlusShift` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSupportIteratedCones` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLift` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DQCoheratorAdjunction` | 21 | 4 | proof |
| `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairsAux` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeComplexHomologyUpperSemicontinuous` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalStrictPerfectStalkProjectiveModel` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectComplexDescent` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDerivedTensor` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectStalkDerivedIsoSpread` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentDistinguishedTriangle` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SpecFiniteProductFields` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange` | 21 | 1 | proof |
| `Sheaf.FieldTheory.PthRootsExtensionDegree` | 21 | 1 | proof |
| `Sheaf.Paper.CartierEquality` | 21 | 1 | proof |
| `Sheaf.Paper.CechCupProduct` | 21 | 2 | proof |
| `Sheaf.Paper.CechRefinementCochainMap` | 21 | 1 | proof |
| `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra` | 21 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientPresentation` | 21 | 1 | proof |
| `Sheaf.RingTheory.DirectedUnionSubringsFlatModule` | 21 | 1 | proof |
| `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat` | 21 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiConnectingMapNaturality` | 21 | 1 | proof |
| `Sheaf.RingTheory.PthRootPresentationDifferentials` | 21 | 1 | proof |
| `Sheaf.RingTheory.RegularQuotientIdealIntersection` | 21 | 1 | proof |
| `Sheaf.RingTheory.StablyFreeComplexLift` | 21 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationColimit` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorTransitivity` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.RhomGlobalSections` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexLiftClassProjective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectIntoSupportPowerTorsion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperSupportDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 22 | 1 | proof |
| `Sheaf.CategoryTheory.TowerSplitEnvelope` | 22 | 1 | proof |
| `Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel` | 22 | 1 | proof |
| `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra` | 22 | 1 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocusOpen` | 22 | 1 | proof |
| `Sheaf.RingTheory.TransitivityGamma` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.AcyclicLift` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` | 23 | 2 | proof |
| `Sheaf.Algebra.Homology.AffineDifferentialColimitDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectChainMapDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuity` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomGap` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | 23 | 1 | proof |
| `Sheaf.FieldTheory.FieldExtensionCompleteIntersectionSubalgebras` | 23 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiRegularSequenceLeftInjective` | 23 | 1 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocalDimension` | 23 | 1 | proof |
| `Sheaf.Algebra.FiniteProjectiveTorAcyclic` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BalancedDerivedTensorModel` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.RingTensorCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFlatModuleDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 24 | 2 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteRelationDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectThickClosure` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QcOpenDerivedLift` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.CompactFactorThroughThick` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleFiniteSupport` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleSupportStep` | 24 | 1 | proof |
| `Sheaf.RingTheory.ConePseudoCoherent` | 24 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Projective` | 24 | 5 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorActionNaturality` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSummand` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.RightLocalizationHomColimit` | 25 | 1 | proof |
| `Sheaf.RingTheory.ColimitCategoryFpAlgebras` | 25 | 1 | proof |
| `Sheaf.RingTheory.ColimitEventuallyFlat` | 25 | 1 | proof |
| `Sheaf.RingTheory.FlatModuleAtPrime` | 25 | 1 | proof |
| `Sheaf.RingTheory.LimitModuleFinitePresentation` | 25 | 1 | proof |
| `Sheaf.RingTheory.OpenFlatLocus` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSummand` | 26 | 1 | proof |
| `Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` | 27 | 2 | proof |
| `Sheaf.Algebra.LimitFinitePresentation.Core` | 27 | 1 | proof |
| `Sheaf.Algebra.TorOneSurjectiveChangeRings` | 27 | 1 | proof |
| `Sheaf.RingTheory.TorIdealKernelNaturality` | 27 | 1 | proof |
| `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle` | 27 | 1 | proof |
| `Sheaf.Paper.FreeComplexExtendFamily` | 29 | 1 | proof |

Waiting, not claimable: 12 modules whose proof uses a node that has no Lean declaration yet.

| module | distance to a target | sorry |
|---|---|---|
| `Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus` | 3 | 1 |
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | 3 | 4 |
| `Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic` | 6 | 1 |
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | 8 | 1 |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero` | 8 | 1 |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | 8 | 1 |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | 8 | 1 |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | 8 | 1 |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | 8 | 2 |
| `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities` | 9 | 1 |
| `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare` | 9 | 1 |
| `Sheaf.RingTheory.HopfAlgebra.AugmentationHeight` | 13 | 1 |
