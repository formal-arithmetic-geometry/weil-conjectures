# Work queue

443 items; claim with `tools/claim.py next <group> [--stage N]`.

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

## Stage 3: modules to prove (413)

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
| `Sheaf.AlgebraicGeometry.EtaleTensorSections` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIdealPowerSupportedOnClosed` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageEventualZero` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveGraphTwistVanishing` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentGenericFilteredSource` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPullbackRows` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiTargetComparison` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment` | 10 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` | 10 | 4 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CokernelTuplePullbackLocalFreeCover` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LinearCechSheafConstruction` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedStructureIdealProductIso` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientBaseChange` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentedSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleRetraction` | 12 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.ExtResolutionDerivedConnecting` | 12 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenComparisonCertificateDegree` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationStalkKernel` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerTensorImageLift` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionHomotopy` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` | 13 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.RightDerivedTriangleConnecting` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyPullbackComparison` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientComposition` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientLeg` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FixedAbelianDescendedSectionLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassLinear` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT` | 14 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.RHomDerivedRoofShift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCoefficientProductTransitions` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassTopComparison` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCoherence` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TargetSectionClassRestriction` | 15 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof` | 15 | 1 | proof |
| `Sheaf.RingTheory.KoszulExtRoofRepresentatives` | 15 | 1 | proof |
| `Sheaf.RingTheory.KoszulRoofComparisonIndependence` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackCoherenceExtend` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSheafificationTensorVanishingTest` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafAffineComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafLocalContraction` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleInverseImageUnitEventualEquality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionPullbackCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageCompletedComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexSingleNaturality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedResolutionEvaluation` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionScalarMap` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AbelianRawPullbackIdentity` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePushoutModuleSectionPresentation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeBaseCoordinates` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeSurjective` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 6 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyThetaAcyclic` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz` | 17 | 1 | proof |
| `Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent` | 17 | 1 | proof |
| `Sheaf.Paper.EtaleCETotalizeAugmentedComparison` | 17 | 1 | proof |
| `Sheaf.RingTheory.BoundedFiniteFreeResolution` | 17 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewise` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIntersectionFiniteType` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineRestrictionIso` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalSystemClosedSupportPushforward` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftCompatibility` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectThickClosure` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrefixDeletionExistence` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjGradedModuleChartPrincipalLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeDifferentialsAffineSectionsMapInjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsSingle` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | 18 | 1 | proof |
| `Sheaf.RingTheory.Derivation.PowerSeriesPolynomialDifferential` | 18 | 1 | proof |
| `Sheaf.RingTheory.FlatFinitePresentationModel` | 18 | 1 | proof |
| `Sheaf.RingTheory.PopescuUnpaddedCoefficientChart` | 18 | 1 | proof |
| `Sheaf.RingTheory.SyntomicEquationCountComparisonDimension` | 18 | 1 | proof |
| `Sheaf.RingTheory.TatePurelyInseparableClosureQuotientFinite` | 18 | 1 | proof |
| `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenSupportedHomologyApproximation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveBoundaryExactness` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveCycleClassEpi` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientComparisonBound` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineLiftInjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionAffineNaturalComparison` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalMapTorsionFiniteDetection` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction` | 19 | 2 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenModuleImageAmalgamation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSummand` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardCupPairingBaseChange` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRankMatchOrdinaryRanks` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonExact` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitClassPullback` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkFiniteFree` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledFiniteGraphEpi` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CompactFactorThroughThick` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteCycleDerivedComparison` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.SingleHomologyShiftComparison` | 19 | 1 | proof |
| `Sheaf.RingTheory.ProjectiveSymmetricCoefficientIntersection` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummand` | 20 | 1 | proof |
| `Sheaf.Algebra.Homology.TensorHomologyMapBijective` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineCompletionBaseChangeUnit` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFormalMapPresentation` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineMapAnnihilationSheafification` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSpecTransport` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechStageLifting` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomComparisonSquare` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomHomologyComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoCoherentModuleExtension` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsAlgebraComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectJumpLoci` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectTensorFiniteRelativeTor` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupCochain` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 3 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSummand` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationLocalDescent` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergConeGradedSplitInjection` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitStageAbelianKanCocone` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle` | 20 | 1 | proof |
| `Sheaf.FieldTheory.PIndependentInsert` | 20 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsCanonicalColimitCore` | 20 | 1 | proof |
| `Sheaf.Paper.NoetherianBoundedCoverDescent` | 20 | 1 | proof |
| `Sheaf.RingTheory.ComparisonMapBaseChangeSystem` | 20 | 1 | proof |
| `Sheaf.RingTheory.ComparisonMapFiniteStage` | 20 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingIsogeny` | 20 | 2 | proof |
| `Sheaf.RingTheory.PowerSeriesCohenFormallySmoothAdic` | 20 | 2 | proof |
| `Sheaf.RingTheory.WellOrderedPresentationComponentData` | 20 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.FlatBaseDerivedTensorComparison` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorSectionNaturality` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomKFlat` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` | 21 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineSourceGeometricIrreducibilityShrink` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompatibleImmersionGluing` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineIdealClassQ` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalAssociatedGradedMultiplication` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsAffineRestrictionDictionary` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelBilinearActionExists` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericOpenGeometricFibreDensity` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageResolutionNaturality` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorQuasicoherent` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtOffRankStalk` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatDiscriminantBranchSupport` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatSingletonFibreChart` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesTestFiniteExtensionFlat` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorRootModelNormal` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenSectionsRestrictionComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperDirectImageTensorLowerBound` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentDistinguishedTriangle` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackStalkTensorFlat` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeOpenGluing` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkTorDimensionLocallyUniform` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.UniversalThickeningCartesianAtlasCore` | 21 | 1 | proof |
| `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra` | 21 | 1 | proof |
| `Sheaf.Paper.TorsionModuleFlatBaseChangeIso` | 21 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientDescent` | 21 | 1 | proof |
| `Sheaf.RingTheory.ClosedFiberDefectDerivationExtension` | 21 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingData` | 21 | 8 | proof |
| `Sheaf.RingTheory.FormalGlueingEquivalence` | 21 | 1 | proof |
| `Sheaf.RingTheory.NoetherNormalizationOverDomainSurjectiveCore` | 21 | 1 | proof |
| `Sheaf.RingTheory.PolynomialLocalFlatQuotientDescent` | 21 | 1 | proof |
| `Sheaf.RingTheory.PopescuQuotientBasisEnlargement` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.RingBoundedProjectiveExtension` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.RingProjectiveInternalHomExact` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange` | 22 | 1 | proof |
| `Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLocalLift` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexLiftClassProjective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteRetractTensorComplexTerms` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineUnion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectComplexDescent` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDerivedTensor` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechHorizontalSquare` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechRegroupDifferential` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativelyFlatModulePullback` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 22 | 1 | proof |
| `Sheaf.Paper.FormalGlueingCanonicalMaps` | 22 | 4 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientPresentation` | 22 | 1 | proof |
| `Sheaf.RingTheory.CompleteIntersectionPresentationStableConormal` | 22 | 1 | proof |
| `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra` | 22 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingComplexExact` | 22 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingH0Localization` | 22 | 1 | proof |
| `Sheaf.RingTheory.GeometricallyRegularDifferentialFamily` | 22 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesParameterQuotient` | 22 | 2 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocusOpen` | 22 | 1 | proof |
| `Sheaf.RingTheory.RegularQuotientIdealIntersectionAux` | 22 | 1 | proof |
| `Sheaf.RingTheory.TorsionExtensionFlatDescent` | 22 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationColimit` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AcyclicLift` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` | 23 | 2 | proof |
| `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.TotalFreeFiltrationEvenQuotientBijective` | 23 | 1 | proof |
| `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechTotalRegrouping` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedScalarConeSplit` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarConeStalkVanishing` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorRoofTransposition` | 23 | 1 | proof |
| `Sheaf.CategoryTheory.TowerSplitEnvelope` | 23 | 1 | proof |
| `Sheaf.RingTheory.ConormalModulePrincipalLocalization` | 23 | 1 | proof |
| `Sheaf.RingTheory.CyclicExtensionFlatDescent` | 23 | 1 | proof |
| `Sheaf.RingTheory.DifferentialCoordinatesCotangentIndependent` | 23 | 1 | proof |
| `Sheaf.RingTheory.DirectSumExtensionAssembly` | 23 | 1 | proof |
| `Sheaf.RingTheory.FlatPolynomialAppendTensorFibre` | 23 | 1 | proof |
| `Sheaf.RingTheory.QuasiFiniteLocalDimension` | 23 | 1 | proof |
| `Sheaf.RingTheory.TorsionCyclicPresentation` | 23 | 1 | proof |
| `Sheaf.RingTheory.TorsionHomFlatComparison` | 23 | 1 | proof |
| `Sheaf.Algebra.ExtOneDirectSum` | 24 | 1 | proof |
| `Sheaf.Algebra.FiniteProjectiveTorAcyclic` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDifferentialColimitDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectChainMapDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BalancedDerivedTensorModel` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedHomExactColumns` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexMappingConeDifferential` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.RingTensorCohomology` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor` | 24 | 1 | proof |
| `Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectTruncationTriangle` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 24 | 2 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenDifferenceDiagram` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuity` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomGap` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSupportAffineOpenTorsion` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` | 24 | 1 | proof |
| `Sheaf.Paper.CyclicExtensionCocycle` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleFiniteSupport` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleSupportStep` | 24 | 1 | proof |
| `Sheaf.RingTheory.PresentationsHomotopyEquivalent` | 24 | 1 | proof |
| `Sheaf.RingTheory.TransitivityGamma` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorActionNaturality` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.RhomGlobalSections` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFlatModuleDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteRelationDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QcOpenDerivedLift` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.RightLocalizationHomColimit` | 25 | 1 | proof |
| `Sheaf.FieldTheory.FieldExtensionCompleteIntersectionSubalgebras` | 25 | 1 | proof |
| `Sheaf.RingTheory.ConePseudoCoherent` | 25 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiRegularSequenceLeftInjective` | 25 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Projective` | 25 | 5 | proof |
| `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat` | 26 | 1 | proof |
| `Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitCategoryFpAlgebras` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitEventuallyFlat` | 26 | 1 | proof |
| `Sheaf.RingTheory.FlatModuleAtPrime` | 26 | 1 | proof |
| `Sheaf.RingTheory.LimitModuleFinitePresentation` | 26 | 1 | proof |
| `Sheaf.RingTheory.OpenFlatLocus` | 26 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure` | 27 | 1 | proof |
| `Sheaf.RingTheory.FlatOfLocalCriterionBaseChange` | 27 | 1 | proof |
| `Sheaf.Algebra.LimitFinitePresentation.Core` | 28 | 1 | proof |
| `Sheaf.Algebra.TorOneSurjectiveChangeRings` | 28 | 1 | proof |
| `Sheaf.RingTheory.TorIdealKernelNaturality` | 28 | 1 | proof |
| `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle` | 28 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps` | 29 | 1 | proof |
| `Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel` | 29 | 1 | proof |
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
