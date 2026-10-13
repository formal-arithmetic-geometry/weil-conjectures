# Work queue

263 items; claim with `tools/claim.py next <group> [--stage N]`.

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

## Stage 3: modules to prove (233)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 26 | 0 | repair |
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
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | 12 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitAffineStageTailColimit` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionOpenScalarComparison` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionTwistCohomologyBound` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ClosedImmersionTwistVanishingStep` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictedLiftHomology` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPullbackHomologySections` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismFaces` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientTargetTensorSurjective` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentIdealPowerTorsionFreeProduct` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentOpenSectionCarrier` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NoetherianProperBoundedCoherentImage` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoefficientTargetTensorDecoder` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeTargetLerayComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IdealPowerAffineDenominatorMap` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomComparison` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleTransitionLaws` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleCoherence` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalizedExistence` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationTransfer` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCommonRepresentative` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCycleRealization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechScalarTransport` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleAffineTensorSectionsEquiv` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizationEvaluation` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRange` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSplitFormalTest` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorDegreewiseIso` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechSheafSingletonContraction` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedSectionFullyFaithful` | 19 | 1 | proof |
| `Sheaf.Paper.EtaleCENormalizedRepresentativeCohomology` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationDiagonalBlock` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationPreDifferential` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection` | 20 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 2 | proof |
| `Sheaf.Algebra.Homology.HomTensorDifferentialSummandPure` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineData` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulCechLocalizedBoundary` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation` | 21 | 1 | proof |
| `Sheaf.RingTheory.PopescuCoefficientInduction` | 21 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedInternalHomShiftComparison` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CompletedAffineSectionsPowerTorsion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteEtaleModel` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeFactorization` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDirectImage` | 22 | 1 | proof |
| `Sheaf.RingTheory.ComparisonTensorLocalSystem` | 22 | 1 | proof |
| `Sheaf.RingTheory.PBasisComplementMonomialBasisLinearIndependent` | 22 | 1 | proof |
| `Sheaf.RingTheory.PBasisComplementMonomialBasisSpanning` | 22 | 1 | proof |
| `Sheaf.RingTheory.Smooth.AugmentationFirstOrderCoordinates` | 22 | 1 | proof |
| `Sheaf.RingTheory.Smooth.AugmentationPolynomialTruncations` | 22 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenRestrictionKFlat` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineModelTensorPullbackStalk` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulExtCoefficientAffineModel` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenAugmentedIdentityClass` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulOpenStructureEvaluation` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtPullbackLocalFrame` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalFiniteFreeScalarHomology` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedResidueHomologySheafRestriction` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineDepthTwoBoundaryProperty` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineLocallyFreeModelCore` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionRestrictionTransport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardOrdinaryRawCoordinates` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorStalkGlobalHomology` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorRoof` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StrictPerfectRelativeTensorTermsFlat` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 4 | proof |
| `Sheaf.Paper.CechHorseshoeLiftClass` | 23 | 1 | proof |
| `Sheaf.RingTheory.PopescuUnscaledUnitBasis` | 23 | 1 | proof |
| `Sheaf.Algebra.Homology.FreeRestrictionTorBound` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.OpenRestrictionTensorNatural` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisSectionsDerivedUnit` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineIntersectionQuotientsStalk` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumBaseChangeComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BoundedGradedModuleMapDescent` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineSectionQuotients` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedOpenKFlatTensorRestriction` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.BoundaryMaximalNotAssociated` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproductComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PullbackTensorUnitSection` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeIdentity` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenStalkConjugacy` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso` | 24 | 1 | proof |
| `Sheaf.CategoryTheory.Abelian.HorseshoeComparisonBoundary` | 24 | 1 | proof |
| `Sheaf.Paper.AffineOpenRepresentingCoverDescent` | 24 | 1 | proof |
| `Sheaf.Paper.AffineOpenSectionsEventualCompatibility` | 24 | 1 | proof |
| `Sheaf.Paper.BoundaryHorseshoeBoundaryIdentification` | 24 | 1 | proof |
| `Sheaf.Paper.EtaleAbelianLocalUnitRepresentatives` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceModel` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeFiltration` | 25 | 2 | proof |
| `Sheaf.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineCoverIdealStalk` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualComplexComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePolynomialLocalizedTorOfStalkwise` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCoordinateRepresentatives` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumStalkConjugacy` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparisonLeft` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExternalSectionsOpenComparison` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatFibreDimensionStrata` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.GenericFibreHypersurfaceFunctionFieldModel` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectDescentCommonLocalModels` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalAffineRectangleExact` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComplexes` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRightCechProductExact` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalRightCechTensorExact` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRightCechCupHomology` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionMateAffineChartCertificate` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ReducedFlatAffinePreparation` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVRestrictionSquares` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkEquivalence` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons` | 25 | 1 | proof |
| `Sheaf.RingTheory.LocalizedPolynomialFiniteProjectiveDimension` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.BaseTensorDerivedComparison` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.TorIndependentTensorAugmentation` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatModuleDescentPreorderStage` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenStalkFreeMapOneLift` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenStalkRestrictionTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementPairing` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupRealizationEvaluation` | 26 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionRealization` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineChartScalarTransport` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedOpenUnionSESPresentation` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationSectionAffineOpenVanishing` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTensorCohomologyAdditiveScalar` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTensorCohomologyLocalizationSquare` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTensorLocalizationFlat` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTensorTargetFlatExtension` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSheafificationScalar` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationAffineChartModels` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapMapLifting` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal` | 28 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelNormalForm` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectHomPresentation` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison` | 29 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels` | 30 | 1 | proof |
| `Sheaf.Algebra.Homology.DerivedTensorFirstLocalizationModels` | 30 | 1 | proof |

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
