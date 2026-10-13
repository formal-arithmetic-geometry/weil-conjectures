# Work queue

463 items; claim with `tools/claim.py next <group> [--stage N]`.

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

## Stage 3: modules to prove (433)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 20 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
| `Sheaf.CategoryTheory.SiteSystemStrictificationData` | 10 | 1 | disputed |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` | 10 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` | 18 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalizationSheafification` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BirationalLinePushforwardGenericStalk` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChowTwistFiniteCohomology` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleTensorSections` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageEventualZero` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentCokernelRelationsLocal` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentGenericFilteredSource` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiTargetComparison` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LinearCechSheafResolution` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` | 10 | 4 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Cohomology.AbelianCechExtSectionBoundary` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleComplexCoherentFiltrations` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechBaseChangeCoordinates` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentationCompatibility` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalClosedIdealMapExtension` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleComparison` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CechSheafLocalAugmentationKernel` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CechSheafLocalPositiveExact` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitBinarySuccessorCoconeSegment` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate` | 12 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientLaws` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.SourceLocalizedCocycleHomology` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenComparisonCertificate` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechModelAcyclicResolution` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FixedAbelianDescendedSectionLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassRestriction` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleLocalFiniteTor` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientSystem` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSheafificationTorAmplitude` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorPureCofaceFixed` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCoefficientProductTransitions` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionEventualEquality` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility` | 15 | 1 | proof |
| `Sheaf.RingTheory.KoszulExtRoofRepresentatives` | 15 | 1 | proof |
| `Sheaf.RingTheory.KoszulRoofComparisonIndependence` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceBase` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineResolutionSectionBijective` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverseBijective` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageCompletedComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexSingleNaturality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedResolutionEvaluation` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionScalarMap` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural` | 16 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredStationaryCycleComparison` | 16 | 1 | proof |
| `Sheaf.RingTheory.PopescuParameterCoefficientModel` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraCounitHomologyComparisonIsIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlternatingCechAugmentedConstruction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenPushforwardExchange` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePushoutModuleSectionPresentation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeBaseCoordinates` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeTopIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 17 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz` | 17 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure` | 17 | 1 | proof |
| `Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent` | 17 | 1 | proof |
| `Sheaf.Paper.EtaleCETotalizeAugmentedComparison` | 17 | 1 | proof |
| `Sheaf.RingTheory.BoundedFiniteFreeResolution` | 17 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewise` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineModuleFiniteType` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineLimitModel` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleIdealKernelIso` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionAffineComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftCompatibility` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferential` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectThickClosure` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardCupProductLocalCriterion` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjGradedModuleChartPrincipalLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapInjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftCompletion` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteKanUnitRelations` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionEvaluation` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionSheaf` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteRawFiniteEqualityStabilization` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.CompactGeneratorAmbientThick` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteCoconeStationary` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | 18 | 1 | proof |
| `Sheaf.Paper.AffinePerfectKoszulPrincipalUnit` | 18 | 1 | proof |
| `Sheaf.Paper.EtaleCEQuotientPageDescent` | 18 | 1 | proof |
| `Sheaf.RingTheory.Derivation.PowerSeriesPolynomialDifferential` | 18 | 1 | proof |
| `Sheaf.RingTheory.FlatFinitePresentationModel` | 18 | 1 | proof |
| `Sheaf.RingTheory.KoszulComplementaryEquivalences` | 18 | 1 | proof |
| `Sheaf.RingTheory.PopescuSpecialChartSubstitution` | 18 | 1 | proof |
| `Sheaf.RingTheory.PopescuZeroBaseSingleChartPresentation` | 18 | 1 | proof |
| `Sheaf.RingTheory.SyntomicEquationCountComparisonDimension` | 18 | 1 | proof |
| `Sheaf.RingTheory.TatePurelyInseparableClosureQuotientFinite` | 18 | 1 | proof |
| `Sheaf.RingTheory.WellOrderedPresentationKernelFiltration` | 18 | 1 | proof |
| `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorCurryNaturalPure` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummand` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorLocalizedExt` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorSummandRestriction` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenSupportedHomologyApproximation` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.VerticalCutoffComparisonKernelTwoTerm` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AnnihilatorStalkLocalLift` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ArtinReesAffineComparison` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientComparisonBound` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitQuotient` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompatibleEtaleGenericFibreModel` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineLiftInjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleTensorSectionsCokernelExact` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleTensorSectionsLocalSurjectivity` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionPushforwardLimitAppBijective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChangeAlgebra` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction` | 19 | 2 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPushforwardCoherence` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFlatCodimensionOneEtaleNeighbourhood` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationGenericComparison` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenModuleImageAmalgamation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSummand` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalQuotientMultiplicationImage` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonExact` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkFiniteFree` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledAffineCandidate` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitSiteAbelianPairwiseEventualMatching` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.SingleHomologyShiftComparison` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle` | 19 | 1 | proof |
| `Sheaf.Paper.ModuleCohomologyCupProduct` | 19 | 1 | proof |
| `Sheaf.RepresentationTheory.LocallyConstantCochainsStructure` | 19 | 1 | proof |
| `Sheaf.RingTheory.AdjoinSingletonFiniteSplitAlgebra` | 19 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationComparisonSystem` | 19 | 1 | proof |
| `Sheaf.RingTheory.LengthQuotSMulTopFractionFieldSubmodule` | 19 | 1 | proof |
| `Sheaf.RingTheory.ProjectiveSymmetricCoefficientIntersection` | 19 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteProjectiveInternalHomEvaluation` | 20 | 1 | proof |
| `Sheaf.Algebra.Homology.TensorHomologyMapBijective` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CartesianTensorDataComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClass` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPrecomposePus` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorSystem` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerQuotientLocalLifting` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechStageKernel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechStageLifting` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalImmersionLocus` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyFinite` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectJumpLoci` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectTensorBoundedCoherent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectTensorFiniteRelativeTor` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupCochain` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrefixDeletionExistence` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 11 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenSectionsResolutionQuasiIso` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperDirectImageFiniteTor` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSummand` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PushoutRegularModuleComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarPullbackTensorCoefficient` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedRelativeOpenGluing` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationLocalDescent` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.UniversalThickeningCartesianAtlas` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergConeGradedSplitInjection` | 20 | 1 | proof |
| `Sheaf.FieldTheory.PIndependentInsert` | 20 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsCanonicalColimitCore` | 20 | 1 | proof |
| `Sheaf.Paper.BalancedActionAffineSections` | 20 | 1 | proof |
| `Sheaf.Paper.NoetherianBoundedCoverDescent` | 20 | 1 | proof |
| `Sheaf.RingTheory.FibreDimensionLocalizedBound` | 20 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationKerRangeCokernel` | 20 | 1 | proof |
| `Sheaf.RingTheory.FlatClosedFiberPowerSeriesModel` | 20 | 1 | proof |
| `Sheaf.RingTheory.NoetherNormalizationOverDomainSurjective` | 20 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesCohenFormallySmoothAdic` | 20 | 2 | proof |
| `Sheaf.RingTheory.PowerSeriesParameterMapFormallySmoothAdic` | 20 | 1 | proof |
| `Sheaf.RingTheory.SyntomicFibreKernelGenerators` | 20 | 1 | proof |
| `Sheaf.Algebra.Homology.FlatBaseDerivedTensorComparison` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.NatSplitFunctionalsHomotopy` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` | 21 | 3 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomKFlat` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` | 21 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLift` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalAssociatedGradedMultiplication` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelBilinearActionExists` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtOffRankStalk` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalStrictPerfectStalkProjectiveModel` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineEnlargement` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectStalkDerivedIsoSpread` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechBicomplexComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentDistinguishedTriangle` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackStalkTensorFlat` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkTorDimensionLocallyUniform` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` | 21 | 1 | proof |
| `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra` | 21 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientDescent` | 21 | 1 | proof |
| `Sheaf.RingTheory.GeometricallyRegularH1Injective` | 21 | 1 | proof |
| `Sheaf.RingTheory.PolynomialLocalFlatQuotientDescent` | 21 | 1 | proof |
| `Sheaf.RingTheory.PopescuQuotientBasisEnlargement` | 21 | 1 | proof |
| `Sheaf.RingTheory.RegularQuotientIdealIntersection` | 21 | 1 | proof |
| `Sheaf.RingTheory.StablyFreeComplexLift` | 21 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationColimit` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.RhomGlobalSections` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexLiftClassProjective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenGluingObjects` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectComplexDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDerivedTensor` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechHorizontalSquare` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 22 | 1 | proof |
| `Sheaf.CategoryTheory.TowerSplitEnvelope` | 22 | 1 | proof |
| `Sheaf.FieldTheory.PthRootsExtensionDegree` | 22 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientPresentation` | 22 | 1 | proof |
| `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra` | 22 | 1 | proof |
| `Sheaf.RingTheory.DirectedUnionSubringsFlatModule` | 22 | 1 | proof |
| `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat` | 22 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiConnectingMapNaturality` | 22 | 1 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocusOpen` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.AcyclicLift` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` | 23 | 2 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectChainMapDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperSupportDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedScalarConeSplit` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarConeStalkVanishing` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorRoofTransposition` | 23 | 1 | proof |
| `Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel` | 23 | 1 | proof |
| `Sheaf.RingTheory.FlatPolynomialAppendTensorFibre` | 23 | 1 | proof |
| `Sheaf.RingTheory.FractionFieldCompleteIntersectionCotangent` | 23 | 1 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocalDimension` | 23 | 1 | proof |
| `Sheaf.RingTheory.TransitivityGamma` | 23 | 1 | proof |
| `Sheaf.Algebra.FiniteProjectiveTorAcyclic` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDifferentialColimitDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BalancedDerivedTensorModel` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedHomExactColumns` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexMappingConeDifferential` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.RingTensorCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 24 | 2 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuity` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomGap` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSupportAffineOpenTorsion` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.CompactFactorThroughThick` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` | 24 | 1 | proof |
| `Sheaf.FieldTheory.FieldExtensionCompleteIntersectionSubalgebras` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleFiniteSupport` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleSupportStep` | 24 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiRegularSequenceLeftInjective` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorActionNaturality` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFlatModuleDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteRelationDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QcOpenDerivedLift` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.RightLocalizationHomColimit` | 25 | 1 | proof |
| `Sheaf.RingTheory.ConePseudoCoherent` | 25 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Projective` | 25 | 5 | proof |
| `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitCategoryFpAlgebras` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitEventuallyFlat` | 26 | 1 | proof |
| `Sheaf.RingTheory.FlatModuleAtPrime` | 26 | 1 | proof |
| `Sheaf.RingTheory.LimitModuleFinitePresentation` | 26 | 1 | proof |
| `Sheaf.RingTheory.OpenFlatLocus` | 26 | 1 | proof |
| `Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` | 27 | 1 | proof |
| `Sheaf.Algebra.LimitFinitePresentation.Core` | 28 | 1 | proof |
| `Sheaf.Algebra.TorOneSurjectiveChangeRings` | 28 | 1 | proof |
| `Sheaf.RingTheory.TorIdealKernelNaturality` | 28 | 1 | proof |
| `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle` | 28 | 1 | proof |
| `Sheaf.Paper.FreeComplexExtendFamily` | 30 | 1 | proof |

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
