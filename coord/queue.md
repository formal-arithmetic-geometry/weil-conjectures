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
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | 34 | 1 | disputed |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | 0 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | 0 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ComplexTermCohomologyColimit` | 10 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf` | 10 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitReindexTransitionCoherence` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition` | 11 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep` | 12 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenMayerVietorisMaps` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality` | 13 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections` | 14 | 1 | proof |
| `Sheaf.Paper.FiniteStructureMultiplicationLift` | 14 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeRestrictedLiftSectionsFormula` | 15 | 1 | proof |
| `Sheaf.Paper.FiniteStructureUnitLiftExistence` | 15 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` | 16 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` | 17 | 2 | proof |
| `Sheaf.AlgebraicGeometry.FlatBaseChangeModuleLerayComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomotopyBaseChangeCounit` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleCohomologyExtPullbackComparison` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapNaturality` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RestrictedOverSingleUnit` | 17 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapInjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RawModuleAbelianHomMapSurjective` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct` | 18 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedSectionPullbackZero` | 19 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EtaleSingletonTensorPureImage` | 19 | 1 | proof |
| `Sheaf.Algebra.Homology.HomTensorReverseConstruction` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility` | 20 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalPuncturedSplit` | 20 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | 20 | 2 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroApex` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PinnedBaseChangeMateShifts` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation` | 21 | 1 | proof |
| `Sheaf.Paper.EtaleCENormalizedRowPresentations` | 21 | 1 | proof |
| `Sheaf.Paper.EtaleCERowCyclesNaturality` | 21 | 1 | proof |
| `Sheaf.Paper.EtaleCERowOrdinaryComparison` | 21 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AlternatingCechPresheafPositiveInsertion` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairMapLifting` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeFactorization` | 22 | 1 | proof |
| `Sheaf.RingTheory.LocalizedApproximationColimits` | 22 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalBeta` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenRestrictionClosedMonoidal` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechColumnStep` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechCoordinateMap` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetCoordinates` | 23 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor` | 23 | 1 | proof |
| `Sheaf.Paper.CechCupPullbackCompat` | 23 | 4 | proof |
| `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineKoszulCoefficientHomCoordinates` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChange` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalLift` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalSupport` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.AffineDualRestrictionComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedEtaleLifting` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedCoverSectionsComparison` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedGermDetection` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RegularLocalDimensionTwoPuncturedFlatModel` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OrdinaryFlatExchangePrescribedAdjunction` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardTermwiseTargetCoherence` | 24 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison` | 24 | 1 | proof |
| `Sheaf.Algebra.Homology.FiniteStripConeFiltration` | 25 | 1 | proof |
| `Sheaf.Algebra.Homology.StrictlyPerfectHomQuasiIso` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineChartUpperTailLimit` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HomComplexRestrictSchemeNatural` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.InternalHomOverEquiv` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.MixedSectionsCompositionCoherence` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedFiniteOrderApproximation` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesPuncturedIdealDetection` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenRestrictionTensorCounitDescent` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare` | 25 | 1 | proof |
| `Sheaf.RingTheory.LocalizedApproximationCocones` | 25 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualNaturality` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootChartsIndEtaleDescent` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPunctures` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationPoint` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayTransportChart` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenSectionsCohomologyComparison` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeTensorPullbackBalancedNaturality` | 26 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData` | 26 | 1 | proof |
| `Sheaf.RingTheory.ColimitFlatRelationDescent` | 26 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeGlobalComparison` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.AffineBaseChangeTildeStalkComparison` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineBasisDerivedSectionsLowerTailVanishing` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ProjectionMateSchemeIsoTransport` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbedding` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVConePresentation` | 27 | 1 | proof |
| `Sheaf.AlgebraicGeometry.RelativeMVRestrictionTargetCounit` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionAugmentation` | 27 | 1 | proof |
| `Sheaf.Paper.ModuleCupResolutionExistence` | 27 | 1 | proof |
| `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.DerivedRestrictionEvaluationMatePostcompBijective` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.OpenUnionImageComplexExact` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.SchemeDerivedStandardEquivalenceMonoidal` | 28 | 1 | proof |
| `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` | 28 | 1 | proof |
| `Sheaf.RingTheory.PolynomialSuccessorTorBound` | 28 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EquidimensionalFibreOpenPartition` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.EquidimensionalOpenLocalDimension` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.FibreCohenMacaulayLocus` | 29 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential` | 29 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementModelPairing` | 29 | 1 | proof |
| `Sheaf.Paper.ModuleCupGodementStalkContraction` | 30 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelBoundedIndependent` | 31 | 1 | proof |
| `Sheaf.FieldTheory.TriangularFieldModelBoundedSpanning` | 31 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AffinePerfectChainGeometricModels` | 32 | 1 | proof |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore` | 33 | 1 | proof |

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
