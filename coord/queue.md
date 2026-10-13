# Work queue

379 items; claim with `tools/claim.py next <group> [--stage N]`.

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
| `lem-weil-pbc-free-complex-base-lift` | 1026 | none |
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

## Stage 3: modules to prove (348)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 25 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
| `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` | 7 | 0 | repair |
| `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` | 2 | 0 | repair |
| `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison` | 2 | 0 | repair |
| `Sheaf.CategoryTheory.MapExtendHomology` | 16 | 0 | repair |
| `Sheaf.Algebra.Homology.TensorBicomplex` | 14 | 0 | repair |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` | 17 | 0 | repair |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` | 18 | 1 | repair |
| `Sheaf.Paper.CartierEquality` | 24 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` | 18 | 0 | repair |
| `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling` | 12 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SheafZeroStalks` | 14 | 0 | repair |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | 9 | 0 | repair |
| `Sheaf.Algebra.Homology.KInjectiveProducts` | 17 | 0 | repair |
| `Sheaf.RingTheory.ProjectiveResolutionExtDegree` | 16 | 0 | repair |
| `Sheaf.RingTheory.ZariskisMainAway` | 10 | 0 | repair |
| `Sheaf.Topology.RingedModuleSkyscraper` | 10 | 0 | repair |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` | 8 | 0 | repair |
| `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf` | 10 | 0 | repair |
| `Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf` | 11 | 0 | repair |
| `Sheaf.CategoryTheory.SiteSystemStrictificationData` | 10 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `Sheaf.RingTheory.TorOneSurjectiveFlatMiddle` | 32 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalDenominators` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyPrincipalTorsion` | 9 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageTailColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LerayAcyclicAdditiveNaturality` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineRestrictedTwistVanishing` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GroupScheme.TwoParameterTranslationAction` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` | 13 | 2 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealTensorRestrictedMultiplicationImage` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleRestrictionMap` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleSignedSection` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorUnitOpenDegreeZero` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineIdealIntersectionInclusion` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientSourceAffineTensorPresentation` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientTargetAffineTensorPresentation` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleFirstSortingBoundary` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrderedCechModuleSecondSortingBoundary` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleRestrictedAbelianNaturalIso` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TailOpenCohomologyLegNaturality` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismFaces` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeLocalHomZero` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteFreeLocalStalkMapLift` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverAbelianComplexData` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TailOpenCohomologyArrowLaws` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TargetSectionClassRestriction` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientComparisonConstruction` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechInverseImage` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleCoefficientProductIdentityComponent` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleInverseImageUnitEventualEquality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleOpenSquareDiagramIdentity` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechNormalizedCoface` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleRestrictionStalkIso` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeLeg` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleConeNaturality` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenPseudoCoherentLocalizationPoint` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.RawRestrictedSectionsUnitZero` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionsHomologyScalar` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.RingTheory.FiniteLocalizationFreeStep` | 17 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafInsertionIdentities` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonRetraction` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonProductRing` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineSingletonTensorSectionsSpan` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleResolutionHomologyExt` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLocalPairing` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.CategoryTheory.RightDerivedSingleUnitShiftTransport` | 18 | 1 | proof |
| `Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages` | 18 | 1 | proof |
| `Sheaf.RingTheory.SyntomicCodimensionLocalKernelGenerators` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewiseConstruction` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewiseIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomIdealPowerEventuallyZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentHomIdealPowerExtension` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionZeroTransport` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteTypeAffineGenerators` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TameRootProductResidueSeparable` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjChartRestrictionIsLocalized` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummand` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineAlgebraUpperTruncationEdge` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotientTransitionExactBound` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompleteBaseAlgebraization` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineTransport` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalGraphFirstQuotientEpi` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorBoundary` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPreDifferential` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationSourceBiproduct` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 2 | proof |
| `Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarInverseImageCompositionCoherence` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient` | 20 | 1 | proof |
| `Sheaf.FieldTheory.IntersectionSubfieldsDifferentialsKernel` | 20 | 1 | proof |
| `Sheaf.FieldTheory.IntersectionSubfieldsDifferentialsPowers` | 20 | 1 | proof |
| `Sheaf.RingTheory.ComparisonMapBaseChangeSystem` | 20 | 1 | proof |
| `Sheaf.RingTheory.PopescuCoefficientRescaling` | 20 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesSubringFiniteBasis` | 20 | 1 | proof |
| `Sheaf.RingTheory.PowerSeriesSubringIntersection` | 20 | 1 | proof |
| `Sheaf.RingTheory.PrincipalPrimeQuotientFractionFinite` | 20 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CechH1Injective` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedLowerTruncationCycleFormula` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalAffineSectionLimit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalModuleQuotientAffineProjectionKernel` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GlobalHomShiftedHypercohomology` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtCoefficientStalkIso` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtExterior` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeCounit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageTestSections` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardPairingComposition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageFirst` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest` | 21 | 1 | proof |
| `Sheaf.FieldTheory.IntersectionSubfieldsSubspace` | 21 | 1 | proof |
| `Sheaf.FieldTheory.PIndependentDifferentialsIndependent` | 21 | 1 | proof |
| `Sheaf.Paper.BoundaryCechCompatibility` | 21 | 1 | proof |
| `Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz` | 21 | 1 | proof |
| `Sheaf.Paper.SquareZeroQuotientLocalAction` | 21 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingMapToAlgebraization` | 21 | 1 | proof |
| `Sheaf.RingTheory.PopescuQuotientBasisEnlargement` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.BoundedProjectiveRestrictionTorAmplitude` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulScalarExtComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineGlobalComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerLocalMapsEventuallyAgree` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomChainClassNaturality` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenHomIdentityEvaluation` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoLocallyFreeModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionHomGluing` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorStalkLocalModelHomology` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedOverlapRestrictionData` | 22 | 1 | proof |
| `Sheaf.Paper.AffineOpenInverseImageUnitRepresentatives` | 22 | 1 | proof |
| `Sheaf.Paper.BoundaryCechInjectiveMiddle` | 22 | 1 | proof |
| `Sheaf.Paper.EtaleSectionZeroNeighbourhood` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexGlobalHomotopy` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffineRight` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorFiniteCover` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatClosedFibreInterior` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalKernelRepresentativeProduct` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericHypersurfaceGeometricIrreducibilitySpread` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineSectionAssociatedStalk` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomEquality` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomExtension` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FlatPowerSeriesChartGenericImage` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesDepthTwoBaseChange` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootProductChartStalkLocalization` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothSectionCompletionChart` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantEvaluationEtaleFibre` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionLocalization` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RadicialGenericReducedPreparation` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeOpenDifferenceDiagram` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarCupZeroGlobalSections` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarPullbackZeroGlobalSections` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenNestedComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenStalkCondition` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnitNaturality` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TorsionCommonOpenComparisonMap` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 4 | proof |
| `Sheaf.RingTheory.FormalGlueingCanonicalFunctor` | 23 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingEssentialSurjectivity` | 23 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingMorphismLifting` | 23 | 1 | proof |
| `Sheaf.RingTheory.HenselianFiniteEtaleFieldLift` | 23 | 1 | proof |
| `Sheaf.RingTheory.HenselianFiniteEtaleMapBijective` | 23 | 1 | proof |
| `Sheaf.RingTheory.TorVanishingLocalizedAlgebra` | 23 | 1 | proof |
| `Sheaf.RingTheory.TorVanishingLocalizedBase` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.BaseDerivedTensorLocalizedNaturality` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.MixedTotalTensorAssociatorDescent` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.MixedTotalTensorAssociatorNaturality` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentKFlatTensorComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulSectionColimit` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ChosenModuleFlatProperStage` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFinitePresentationBinaryGluing` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseLift` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkDegreewiseShrink` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechExact` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRightCechExact` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineLocus` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QCqsProjectionMateShiftedUnit` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction` | 24 | 1 | proof |
| `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime` | 24 | 1 | proof |
| `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition` | 24 | 1 | proof |
| `Sheaf.RingTheory.PthRootCotangentDimension` | 24 | 1 | proof |
| `Sheaf.RingTheory.ResidueConormalSnakeSequence` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceModel` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AdjointTensorAnnihilatorTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineRegularStalkComparisonBijective` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineRegularStalkScalar` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalDescentDatum` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkReverseComponentsLift` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation` | 25 | 1 | proof |
| `Sheaf.FieldTheory.PthRootNotMemPreviousAdjoin` | 25 | 1 | proof |
| `Sheaf.Paper.ModuleCupPairingExists` | 25 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionInvariance` | 25 | 1 | proof |
| `Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting` | 25 | 1 | proof |
| `Sheaf.RingTheory.FiniteRankCoefficientCorrection` | 25 | 1 | proof |
| `Sheaf.RingTheory.FractionFieldCompleteIntersectionCotangent` | 25 | 1 | proof |
| `Sheaf.Algebra.FiniteFamilyModuleMapEqualityColimit` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectChainMapEqualityDetection` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.AffinePerfectGradedHomDescent` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexDualTotalComparison` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineLiftEventualFreeKernels` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenUnionAdjunctionTriangle` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectOpenStalkRetractMapEquality` | 26 | 1 | proof |
| `Sheaf.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupCanonicalHZeroIdentification` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementPairing` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupHZeroIdentification` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` | 26 | 1 | proof |
| `Sheaf.RingTheory.EtaleFiniteFactorDecomposition` | 26 | 1 | proof |
| `Sheaf.RingTheory.FormalGlueingLocalizedChartTuple` | 26 | 1 | proof |
| `Sheaf.RingTheory.IdealPowerHomLift` | 26 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationMapCanonical` | 27 | 1 | proof |
| `Sheaf.Algebra.FinitePresentationRestrictedHomColimit` | 27 | 1 | proof |
| `Sheaf.Algebra.FiniteRelationCokernelColimit` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.FinitePresentationColimitRetraction` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenPerfectSourceModel` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenRealizationScalar` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineOpenSupportedTargetModel` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion` | 27 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelEvaluationKernel` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenFiniteProjectiveTilde` | 28 | 1 | proof |
| `Sheaf.RingTheory.CompatibleModuleModelDescent` | 28 | 1 | proof |
| `Sheaf.RingTheory.FiniteTypeApproximationFlatLoci` | 28 | 1 | proof |
| `Sheaf.RingTheory.TensorModelAlgebraDescent` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalLocalizationSheafTorBounds` | 30 | 1 | proof |
| `Sheaf.RingTheory.ColimitMaximalKernelDescent` | 30 | 1 | proof |
| `Sheaf.RingTheory.FinitePresentationModuleBaseChangeDiagram` | 30 | 1 | proof |
| `Sheaf.RingTheory.FlatPointNoetherianModel` | 30 | 1 | proof |
| `Sheaf.RingTheory.BaseChangeIdealKernelGenerators` | 32 | 1 | proof |
| `Sheaf.RingTheory.LocalizationIdealKernelGenerators` | 32 | 1 | proof |
| `Sheaf.RingTheory.TorIdealComparisonCompatibility` | 33 | 1 | proof |
| `Sheaf.RingTheory.TorIdealConnectingFormula` | 33 | 1 | proof |

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
