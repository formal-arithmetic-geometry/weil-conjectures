# Work queue

208 items; claim with `tools/claim.py next <group> [--stage N]`.

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
| `lemma-weil-pbc-stein-connectedness` | 2006 | rests_on_sorry |
| `thm-weil-pbc-stein-inputs` | 2007 | sorry_here |
| `sbc-prop-extension-by-zero-and-arbitrary-base-change` | - | none |
| `lem-pc-section-cohomology-untwisted-comparisons` | - | none |
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

## Stage 3: modules to prove (177)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 27 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
| `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps` | 38 | 0 | repair |
| `Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps` | 38 | 0 | repair |
| `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso` | 7 | 0 | repair |
| `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` | 2 | 0 | repair |
| `Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison` | 2 | 0 | repair |
| `Sheaf.CategoryTheory.MapExtendHomology` | 16 | 0 | repair |
| `Sheaf.Algebra.Homology.TensorBicomplex` | 14 | 0 | repair |
| `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal` | 17 | 0 | repair |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore` | 18 | 0 | repair |
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
| `Sheaf.Paper.FiniteStructureAlgebraLift` | 11 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 30 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitReindexTransitionCoherence` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictionResolutionLiftSections` | 16 | 1 | proof |
| `Sheaf.Paper.FiniteStructureProductCompatibility` | 16 | 1 | proof |
| `Sheaf.Paper.FiniteStructureProductCore` | 16 | 1 | proof |
| `Sheaf.Paper.FiniteStructureUnitQuotientSystem` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapNaturality` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleUnit` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapSurjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective` | 19 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedSourceComparisonInjective` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorReverseConstruction` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalZeroSliceSplit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroApex` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` | 21 | 1 | proof |
| `Sheaf.Paper.EtaleCERowOrdinaryComparison` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonInheritance` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PinnedDerivedAdjunctionShifts` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorStalkComparisonSquares` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.UniversalH0ProjectiveNormalization` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDenseEtaleGoingDown` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechColumnStep` | 23 | 1 | proof |
| `Sheaf.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 3 | proof |
| `Sheaf.RingTheory.LocalizedModuleColimitComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalSupport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveHomology` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionAugmentation` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionBijective` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionDifferential` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsExtensionUnitNormalization` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsCompositionCoherence` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonCoherence` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFiniteGluing` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData` | 26 | 1 | proof |
| `Sheaf.RingTheory.CanonicalLocalizedApproximationLimit` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitFlatRelationDescent` | 26 | 1 | proof |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.BalancedTensorComparisonIsIso` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeStalkComparison` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeGradedMapDifferential` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeGradedMapIsIso` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulSignedDualCoefficientSquare` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsKernel` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedThickeningRestrictionIso` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenSectionsCohomologyModel` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenSectionsStructureClass` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionExistence` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeCanonicalGlobalComparison` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisLowerTailSectionsReconstruction` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisLowerTailSectionsStep` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootOrbitDescent` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeCounit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVOpenSquareCounit` | 28 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedCategory.EndpointConePresentation` | 28 | 1 | proof |
| `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionModuleImagePullback` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ReducedGenericFibreMapCore` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons` | 29 | 1 | proof |
| `Sheaf.RingTheory.StrictHenselizationNoetherian` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenTensorHomBijective` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CohenMacaulayFlatQuasiFiniteChart` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PolynomialChartFibreFlatCriterion` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart` | 31 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementCosimplicialExists` | 31 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementIteratePairings` | 31 | 1 | proof |
| `Sheaf.RingTheory.StrictHenselizationCompletionFlat` | 31 | 1 | proof |
| `Sheaf.RingTheory.StrictHenselizationLocalMaximalIdeal` | 31 | 1 | proof |
| `Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat` | 32 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpecifiedModelChainComparison` | 33 | 1 | proof |
| `Sheaf.RingTheory.AssociatedGradedRing` | 33 | 5 | proof |
| `Sheaf.RingTheory.EtaleTripleStrictHenselizationIdentification` | 33 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone` | 34 | 1 | proof |
| `Sheaf.RingTheory.FlatModuleCompletion` | 34 | 1 | proof |
| `Sheaf.RingTheory.StrictHenselizationModPowerFree` | 34 | 1 | proof |
| `Sheaf.RingTheory.LimitFlatModules` | 35 | 1 | proof |
| `Sheaf.Algebra.Homology.MittagLefflerLimitHomology` | 36 | 1 | proof |

Waiting, not claimable: 14 modules whose proof uses a node that has no Lean declaration yet.

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
| `Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint` | 21 | 1 |
| `Sheaf.RingTheory.AssociatedGradedIdealApproximation` | 33 | 1 |
