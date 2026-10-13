# Work queue

366 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (23)

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
| `lem-weil-pbc-free-complex-base-lift` | 1024 | none |
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |
| `sbc-prop-extension-by-zero-and-arbitrary-base-change` | - | none |
| `prop-nagata-relative-proj-functoriality` | - | none |
| `def-nagata-relative-proj` | - | none |
| `lemma-nagata-proj-chart-ring-cocycle` | - | none |
| `lemma-nagata-relative-proj-exists` | - | none |
| `lem-kun-fp-algebra-descent` | - | none |

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

## Stage 3: modules to prove (335)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 24 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
| `Sheaf.CategoryTheory.SiteSystemStrictificationData` | 10 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` | 18 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalLocalization` | 8 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageEventualZero` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenTwistVanishingIndependent` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiSectionUnitEquation` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GabberH0ZariskiTargetComparison` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveFiniteSourceCohomologySegment` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentGenericLocalFreeModel` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentLocalFreeIdealLattice` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GroupScheme.MixedTranslationCoefficients` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentedSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleRetraction` | 12 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenComparisonCertificateDegree` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonBijective` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawComplexPresentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleProjectionHomotopy` | 13 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison` | 13 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.SplitSESCocycleBoundary` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealIntersectionBound` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientLeg` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationSourceStalk` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FixedAbelianDescendedSectionLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealTensorMultiplicationKernelControl` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealTensorRestrictedMultiplicationImage` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InternalHomGermZeroFiniteType` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkLinearMapLocalLiftFinitePresentation` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHom` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCoefficientProductTransitions` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeAffineCanonicalComparisons` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechDegreewiseProjectionDifferential` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCoherence` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TargetSectionClassRestriction` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSheafificationTensorVanishingTest` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleInverseImageUnitEventualEquality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionPullbackCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionScalarMap` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafAffineSections` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafInsertionHomotopy` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeBaseCoordinates` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeSurjective` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 6 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedSectionsUnitZero` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent` | 17 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewise` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjGradedModuleChartPrincipalLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ShortComplexSectionComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | 18 | 1 | proof |
| `Sheaf.RingTheory.Derivation.PowerSeriesPolynomialDifferential` | 18 | 1 | proof |
| `Sheaf.RingTheory.SyntomicEquationCountComparisonDimension` | 18 | 1 | proof |
| `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexCycleLift` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraKInjectiveBoundaryExactness` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientComparisonBound` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DiagonalConormalAffineLiftInjective` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeHomComplexQCCohomology` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalCompletionAffineNaturalComparison` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction` | 19 | 2 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitClassPullback` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledFiniteGraphEpi` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.CompactFactorThroughThick` | 19 | 1 | proof |
| `Sheaf.RingTheory.PopescuRescalingData` | 19 | 1 | proof |
| `Sheaf.RingTheory.TateRootClosureQuotientFinite` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummand` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionConormalAffineTensorCoordinates` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjection` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KInjectiveSectionCycleComparison` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenModuleImageSectionRestriction` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardPairingPullbackCoherence` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 3 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSummand` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates` | 20 | 1 | proof |
| `Sheaf.CategoryTheory.ColimitStageAbelianKanCocone` | 20 | 1 | proof |
| `Sheaf.FieldTheory.PIndependentInsert` | 20 | 1 | proof |
| `Sheaf.Paper.NoetherianBoundedCoverDescent` | 20 | 1 | proof |
| `Sheaf.RingTheory.ComparisonMapBaseChangeSystem` | 20 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorSectionNaturality` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` | 21 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineFormalMapLimitDictionary` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKProjectiveHomComplex` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompatibleImmersionGluing` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalAssociatedGradedMultiplication` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulChainRestrictionFormula` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomChainEvaluation` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorStalkKernelSpan` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoPushforwardHull` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeCounit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeOpenGluing` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectRelativeTensorStalkBound` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` | 21 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsDescent` | 21 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsZeroDetection` | 21 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingMapFromAlgebraization` | 21 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingMapToAlgebraization` | 21 | 1 | proof |
| `Sheaf.RingTheory.PopescuQuotientBasisEnlargement` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexHypercohomology` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulScalarExtComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsFiniteTorOfStalkwise` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsTorBoundStalk` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalCupZeroGlobalSections` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorBijective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelProductSection` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericGeometricallyIntegralAffineChart` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericOpenFibreDensity` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericRadicialGeometricallyReducedModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KInjectiveAlternatingCechAugmentationQuasiIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomChainRepresentatives` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthOneRestrictionInjective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoRestrictionBoundarySurjective` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatTraceDiscriminantGluing` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothSectionPowerSeriesChart` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantFibreEtaleCriterion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDerivedTensor` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechHorizontalSquare` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalCechRegroupDifferential` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperSupportDerivedProjectionFormula` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenAffine` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenTop` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexTargetLocality` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionControlledOverlapCocycle` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.UniversalThickeningOverlapGlueData` | 22 | 1 | proof |
| `Sheaf.RingTheory.ArtinianCoefficientEventualFlatness` | 22 | 1 | proof |
| `Sheaf.RingTheory.CompleteIntersectionPresentationStableConormal` | 22 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingEquivalence` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeSheafStalkRealization` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChosenComplexFlatProperRefinement` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexLiftAcyclicEnlargement` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineCapture` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleSubmoduleBinaryGluing` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointFiniteFlatLift` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenKernelConormalTransport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDescentAffineOpen` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkChainMapLift` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkInverseHomotopiesSpread` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveClassReducedSplitting` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackStalkRelativeFlatExtension` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionMate` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkComparisonSourceTransport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorRoofTransposition` | 23 | 1 | proof |
| `Sheaf.RingTheory.DifferentialCoordinatesCotangentIndependent` | 23 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingComplexExact` | 23 | 1 | proof |
| `Sheaf.RingTheory.NilpotentCoefficientAdjustment` | 23 | 1 | proof |
| `Sheaf.RingTheory.PthRootResidueDimensionBalance` | 23 | 1 | proof |
| `Sheaf.RingTheory.TorsionExtensionFlatDescent` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.AcyclicLiftTailExtension` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BalancedDerivedTensorModel` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedHomExactColumns` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteFreeInternalHomExactSequence` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexMappingConeDifferential` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingDualTermFlat` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.RingExtensionFiniteSupportProduct` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.RingHomExtensionTransport` | 24 | 1 | proof |
| `Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteRelationDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomGap` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison` | 24 | 1 | proof |
| `Sheaf.Paper.TotalResolutionCycleSupportStep` | 24 | 1 | proof |
| `Sheaf.RingTheory.CyclicExtensionFlatDescent` | 24 | 1 | proof |
| `Sheaf.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP` | 24 | 1 | proof |
| `Sheaf.RingTheory.DirectSumExtensionAssembly` | 24 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingH0ChartPowerLift` | 24 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationColimit` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` | 25 | 2 | proof |
| `Sheaf.Algebra.Homology.AffineDifferentialColimitDescent` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedGradedMapColimitDescent` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteChainSquaresColimitDescent` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenLocalizedModel` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 25 | 2 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenIntersectionMateIso` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleDescentAffineCharts` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuity` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHypercohomologyGap` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectSupportAffineModuleModel` | 25 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedCategory.BoundedProjectiveHomPowerTorsion` | 25 | 1 | proof |
| `Sheaf.RingTheory.FiniteLocalizationFreeModel` | 25 | 1 | proof |
| `Sheaf.RingTheory.JacobiZariskiRegularSequenceLeftInjective` | 25 | 1 | proof |
| `Sheaf.RingTheory.PthRootAlgebraLocal` | 25 | 1 | proof |
| `WeilConjectures.AlgebraicGeometry.Cohomology.Projective` | 25 | 5 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteProjectiveModuleColimitDescent` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle` | 26 | 1 | proof |
| `Sheaf.RingTheory.FlatModuleTensorModel` | 26 | 1 | proof |
| `Sheaf.RingTheory.FpModuleTensorModelComparison` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.TensorComparisonStupidTail` | 27 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelPresentation` | 27 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelWeakRegularity` | 27 | 1 | proof |
| `Sheaf.RingTheory.OpenFlatLocus` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact` | 28 | 1 | proof |
| `Sheaf.RingTheory.ColimitMaximalKernelDescent` | 28 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationModuleDiagram` | 28 | 1 | proof |
| `Sheaf.RingTheory.LocalizedBaseChangeIdealKernelSpan` | 29 | 1 | proof |
| `Sheaf.RingTheory.LocalizedBaseChangeQuotientFlat` | 29 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages` | 32 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredQuotientFirstConnecting` | 32 | 1 | proof |
| `Sheaf.CategoryTheory.FilteredHomologyCoupleExactness` | 34 | 1 | proof |

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
