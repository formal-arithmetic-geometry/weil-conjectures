# WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

## Reason

Restore the five theorem proofs lost during upstream sync. Added private proof helpers,
local inference instances, universe declarations and local elaboration controls are
recorded because preflight classifies nondeclaration-command changes conservatively.
Every existing public signature, attribute, public import and non-theorem body remains
unchanged. No target meaning changes. Only the assigned item is edited.

## Old

The five original theorem bodies were `sorry`. Existing construction and assembly:

```lean
theorem constructibleCocone_isFilteredTwoColimit :
    (constructibleCocone X ℓ).IsFilteredTwoColimit where
  essSurjObj := constructibleCocone_essSurjObj X ℓ
  homSurj := constructibleCocone_homSurj X ℓ
  homInj := constructibleCocone_homInj X ℓ

```

## New

The assembly above is unchanged. The five theorem bodies now use the recovered
complete proofs; all added helpers are private and proved. The existing public
non-theorem declarations retain their exact source bodies. The proof-only imports
are not re-exported. The local helper instances do not become persistent instances.

The private Hom-continuity instances supply isomorphism, shift and extension closure.
The exact-derived helpers transport the canonical shift and triangulated structure.
The bounded-factorization and tensor-component lemmas prove the finite-stage Hom
argument. The ambient cocone, its shift and triangulated structures, Hom surjectivity
and single-sheaf models prove object descent by the existing bounded devissage theorem.
Local irreducibility and instance-priority settings share the existing large sheaf,
scalar and derived constructions without replacing their values. `maxSynthPendingDepth`
is set to zero. Canonical sheaf and module monoidal structures are selected locally.
The exact-derived helper applications specify their source and target categories,
so inference does not postpone those category parameters. The tensor-comparison
component proofs use full-faithful cancellation and the identity-composition laws
directly, avoiding simplification of large derived constructions. The factorization
input is packaged with its defining equation in a subtype, and the factorization
and ambient Hom-descent hypotheses have explicit existential types. The single-sheaf
comparison is given an explicit isomorphism type before composition. These local
proof terms avoid expensive elimination against inferred derived-category expressions.
None of these commands exports a new instance or changes an existing definition.

## Users

Read-only `tools/downstream.py` was run with all five theorem names and also with
`--names`; the following table lists all current transitive importers, including
quarantined consumers. Current holder metadata is read from the claim records.
No public declaration or construction changes, so no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | Z6 | Five theorem proofs restored. |
| Sheaf.AlgebraicGeometry.CoconeDerivedComparisonNormalForm | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | G1 | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationProjectionInverse | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | U8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAdicProperBaseChangeRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | F5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperScalarComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | R8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbedded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedCompletion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedResidueComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsEmbeddedStacksCriterion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NormAlgClInternalHomBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | K3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | F1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | H5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TamePairProperGenerators | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarRestrictedTransposeExpansion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaAdic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaField | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Main | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Product | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261024T223355-L-1602497 2026-10-24 (merge of deliver/Z6/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit)
