# Work queue

247 items; claim with `tools/claim.py next <group> [--stage N]`.

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

## Stage 3: modules to prove (216)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 27 | 0 | repair |
| `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap` | 13 | 0 | repair |
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
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 33 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitReindexTransitionCoherence` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPullbackHomologySections` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSections` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveExchangeTargetTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientTargetScalarSpan` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientTargetSectionGenerators` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientIntersectionSectionModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapIsIso` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapNaturality` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationHomology` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NestedOpenSingleDirectImageComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaQuasiIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaClosed` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalSplit` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSquare` | 19 | 1 | proof |
| `Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorReverseConstruction` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaQuasiIso` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PinnedSingleBaseChangeShift` | 20 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 2 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummandPure` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafDifferentialInnerInverse` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafLocalExact` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomEvaluationPostcomposition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomEvaluationPrecomposition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionSurjective` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarForgetPullbackAdjunction` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.RingTheory.ElementwiseFpModuleEquivDescent` | 21 | 1 | proof |
| `Sheaf.RingTheory.TensorModelAlgebraStage` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalEvaluationOpenRestriction` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalTransfer` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationAffineChartSectionsModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationAffineSectionsRealization` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGlobalSections` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeFactorization` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechInjectiveComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechInjectiveTerms` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetComparison` | 22 | 1 | proof |
| `Sheaf.RingTheory.LocalizedApproximationBaseChange` | 22 | 1 | proof |
| `Sheaf.RingTheory.LocalizedApproximationColimits` | 22 | 1 | proof |
| `Sheaf.RingTheory.Smooth.AugmentationPolynomialTruncationsInjective` | 22 | 1 | proof |
| `Sheaf.RingTheory.Smooth.AugmentationPolynomialTruncationsSurjective` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedInternalHomShiftLeft` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenRestrictionKFlat` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalFlatQuotientMateData` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsKFlatComparisonIso` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoBoundaryProperty` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapRestriction` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 4 | proof |
| `Sheaf.RingTheory.ComparisonTensorDiagrams` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.HomComplexShiftRight` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.StalkKFlatTensorHomology` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulCoefficientHomCoordinates` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineModelStalkTensorTransport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexRestrictScheme` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtQuotientFrame` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalFiniteFreeHomologyNatural` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsSquareComparisonCoherence` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTensorFrameRestriction` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate` | 24 | 1 | proof |
| `Sheaf.RingTheory.NoetherianApproximationLocalizedDiagrams` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeFiltration` | 25 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisSectionsResolutionHomologyEpi` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCoordinateRepresentatives` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalSectionsOpenComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenAugmentationCechUnit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenSectionsUnit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedOpenTensorEquivalence` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardTensorComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorPullbackComplexComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore` | 25 | 1 | proof |
| `Sheaf.Paper.EtaleAbelianKanComparisonLocallySurjective` | 25 | 1 | proof |
| `Sheaf.RingTheory.PopescuAlgebraicResidueEnlargement` | 25 | 1 | proof |
| `Sheaf.RingTheory.PopescuTranscendentalResidueEnlargement` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeSourceModel` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalSectionsUnitMapLeft` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldHypersurfaceFunctionFieldModel` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatFibreDimensionStrataCore` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.BoundaryLocalizedFiniteDetector` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDescentOpenEventualModel` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRightRectangleSymmetry` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardLeftCechCupConstruction` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionMateAffineChartTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RadicialSeparatingGenericField` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVRestrictionFirst` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVRestrictionSecond` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionRealization` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitFlatRelationDescent` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.BaseTensorDerivedChainComparison` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineChartScalarTransport` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenStalkUnitMapOneLift` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRectangleSections` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVConePresentation` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupCosimplicialAW` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` | 27 | 1 | proof |
| `Sheaf.RingTheory.PolynomialTorBound` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionZeroAtStage` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedOpenImageComplexComparisons` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionImageComplexExact` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal` | 28 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementCosimplicialInput` | 28 | 1 | proof |
| `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential` | 29 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelReconstructionBijective` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectChainHomPresentation` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows` | 32 | 1 | proof |

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
