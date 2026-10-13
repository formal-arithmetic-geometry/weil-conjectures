# Work queue

179 items; claim with `tools/claim.py next <group> [--stage N]`.

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

## Stage 3: modules to prove (148)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` | 23 | 0 | repair |
| `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap` | 18 | 0 | repair |
| `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` | 21 | 0 | repair |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | 28 | 0 | repair |
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
| `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` | 14 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 1 | disputed |
| `Sheaf.RingTheory.ColimitFlatRelationDescent` | 26 | 1 | disputed |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentCore` | 30 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyContinuity` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitReindexTransitionCoherence` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenBoundaryTransform` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatUnitRawSections` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Cohomology.CartesianUnitCohomologyPullbackComposition` | 16 | 1 | proof |
| `Sheaf.Paper.FiniteStructureProductCompatibility` | 16 | 1 | proof |
| `Sheaf.Paper.FiniteStructureProductCore` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapNaturality` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeChartCohomologyTransport` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounit` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenCoverMapLiftTransport` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedTensorCounitTransport` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitRepresentative` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 2 | proof |
| `Sheaf.Paper.EtaleRowIntegerSections` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationChartMapZeroEventually` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleCanonicalEventually` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTransport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OverlapPairModelTransport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates` | 24 | 1 | proof |
| `Sheaf.Paper.CechCupResolutionRepresentatives` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureCoproduct` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureTriangle` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonShift` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.LocalizedTensorComparisonUnit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization` | 25 | 1 | proof |
| `Sheaf.Paper.CechRefinementResolutionDiagram` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumComparisonCancellation` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumPullbackSquareCoherence` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNaturalComponents` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedPullbackSectionsCounitUnit` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaces` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization` | 26 | 1 | proof |
| `Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisDualMatrix` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsLeftUnitNormalization` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsRightUnitNormalization` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricDirect` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.ResidueKernelUnitMinor` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicPushforwardCoordinates` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVOpenSquareCounit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenOrdinaryComparison` | 28 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeGradedMapSplitEpi` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineHomComparisonMaps` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.DualFiniteFreeQuotientEmbedding` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Modules.QuasiAffineFiniteFreeQuotient` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapTorsionKernel` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingAffineSectionsComparison` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericSourceEtale` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangePrefix` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeTargetTranspose` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChart` | 29 | 1 | proof |
| `Sheaf.Paper.ModuleCupKInjectiveTarget` | 29 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization` | 30 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates` | 30 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineScalarLocalizedTensorSquare` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData` | 30 | 2 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapKernelLocalTorsion` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapResidueQuotientSurjective` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalFiniteLevelLift` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalRestrictionKernel` | 30 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel` | 30 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization` | 31 | 1 | proof |
| `Sheaf.Algebra.Homology.HomologyEvaluationCycleExistence` | 31 | 1 | proof |
| `Sheaf.Algebra.Homology.HomologyEvaluationLocalIso` | 31 | 1 | proof |
| `Sheaf.Algebra.Homology.HomologyEvaluationUniqueness` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisDirectImageBoundary` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate` | 31 | 1 | proof |
| `Sheaf.Paper.GlobalTensorPullbackDerivedData` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit` | 32 | 1 | proof |
| `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization` | 32 | 1 | proof |
| `Sheaf.RingTheory.StrictHenselizationDimension` | 32 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpecifiedModelChainComparison` | 34 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonForward` | 34 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverse` | 34 | 1 | proof |
| `Sheaf.RingTheory.FilteredColimitPrimeChainContraction` | 34 | 1 | proof |
| `Sheaf.RingTheory.FilteredColimitPrimeChainDimensionBound` | 34 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementTensorCoordinatesExists` | 35 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns` | 36 | 1 | proof |

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
| `Sheaf.RingTheory.AssociatedGradedIdealApproximation` | 36 | 1 |
