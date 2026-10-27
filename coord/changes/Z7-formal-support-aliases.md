# formalSupportPullbackAdjunction

## Reason

The formal support module duplicated the completed `CondensedClosedSupportAdjunction` API.
Consolidate its adjunction as an abbreviation of the existing construction, under the
one-definition rule. Retain the original pullback, kernel functor, closed support functor,
inclusion and comparison definitions verbatim. This permits reuse of the proved support
interface without dependent transports between two adjunction presentations.

The pullback functors are definitionally equal: both restrict scalars along the inverse
of `condensedPullbackHom`. The old scalar-equivalence adjunction and the explicit scalar
equivalence used by `supportPullbackAdjunction` have equal counits, since both are identities
after forgetting the module structure. `Adjunction.ext_counit` then identifies them.
Their induced module adjunction units agree: the additional functor associator has identity
components. Consequently the kernels, kernel maps, inclusions and closed-unit comparisons
are the same constructions. In particular the normalized counit and Hom-complex component
formula in the theorem retain their meanings.

The derived proof uses the arbitrary chosen model universe `w`, rather than importing the
fixed-universe conclusion of the completed API. The target declarations in `Challenge.lean`
are untouched. Targets whose statements depend on these definitions should be included
in the definition-change statement review; this is a presentation consolidation, with no
claimed exemption from that review.

## Old

```lean
def formalSupportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    formalSupportPullback Λ f ⊣ lowerStar Λ f :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).comp
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.toAdjunction).ofNatIsoRight
      (comapPullbackHomCompIso Λ f)
```

## New

```lean
abbrev formalSupportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    formalSupportPullback Λ f ⊣ lowerStar Λ f :=
  supportPullbackAdjunction Λ f
```

All other existing definitions, declaration types and docstrings are retained verbatim.
The completed API is a new public import because this abbreviation references it.
The private proved `comparison_eq` accounts for the identity associator in the completed
comparison: its components simplify by `Category.comp_id`.

## Users

The inventory below is the transitive downstream list from `tools/downstream.py` with all
six related support names passed to `--uses`, plus this item. Textual users have been
inspected. The adjunction is consolidated without changing their mathematical meanings; modules that only import
them transitively retain their statements. The ordered remote compile rebuilt the item (44.1 s) and immediate importer
`FormalClosedPullbackProducts` (13.0 s). `FormalClosedSupport` reached the 60-second
limit; the remaining immediate importer was therefore not run by that batch. The earlier
broad check compiled `FormalClosedSupport` and `ClosedSupportConstructible` against the
completed support presentation, but some larger consumers hit elaboration limits.
No claimed clean result is inferred from a timeout.
Their mathematical statements retain the same adjunction unit, verified by the scratch
equality proof.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingProjectionSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingTensorCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingTensorTransposeAssembly` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction` | Z7 | Adjunction alias and theorem proof; other definitions unchanged. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.DeligneLaumon.SmoothAffineConstituentPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | C9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | Q5 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | W2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicProperLocalizingAdjunctionComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | R2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineCompactificationComparisonNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineCounitScalar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineLineCanonicalScalarCounit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerBoundedTransport` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerFiniteEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerFiniteSiteComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerGeometricTransport` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.BrownTowerSite` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CanonicalDiagonalRightDerived` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CartesianSectionData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ChartCounitScalarTransport` | T8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ChartGeometricCounitEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ClosedSupportConstructible` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | V7 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientMapGeometricSquares` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CompactSupportTowerReduction` | J9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | D6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | A2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | Q3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CondensedHomChainRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalBaseSquares` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientCategory` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientDiagrams` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientEndpoints` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFamilyExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFamilyPullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientMaps` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientPullbackEndpoints` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotientLine` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientQuotients` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientScalars` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientSourcePullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientUniformizerReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedDiagramRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedFrame` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedPushSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteRootMap` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalIntegralRootMap` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalNonTorsionBaseChange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalQuotientBaseChange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerCoefficients` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerLimit` | V2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTrace` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTraceIntegrationSystems` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTracePresentationExistence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTraceResultExistence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTraceSingleFaithful` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalTraceSources` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerAnnihilator` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleCtfChartDomain` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleOpenCounitFlatModels` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y7 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.EtaleSumCounitScalar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteAdjointCompositorTransposes` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | P8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteCompactSupportDomains` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalOrientationReduction` | F1 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteDiagonalReductionComparisons` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtensionData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingSmoothLocalFormula` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | M6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | J2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.FormalClosedPullbackProducts` | unclaimed | Direct importer; signature unchanged; ordered compile passed (13.0 s). |
| `Sheaf.Paper.FormalClosedSupport` | unclaimed | Direct importer; signature unchanged; ordered compile timed out; no type error reported. |
| `Sheaf.Paper.FormalClosedSupportII` | unclaimed | Direct importer; original kernel definition retained; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupportIILimits` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | B8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.IntegralDualizingExceptionalUnit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | D8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.LatticeSupportedHomFiniteComparison` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.MateOpenCompactSupportExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.MateOpenProperRestrictionIso` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.MateOpenRestrictionMaps` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NormAlgClInternalHomBaseChange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | W2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NormalizedStageCoefficientCalculus` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.NormalizedSupportEtalePresentation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.OpenExceptionalScalarLocality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.OpenProEtaleCounitScalar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.OrderedCompactificationScalarSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.OrderedTateScalarNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | F6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.P1CounitScalar` | F4 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.P1SplittingScalar` | G1 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | H1 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | H8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | Y5 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProjectiveDiagonalComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProjectiveDiagonalPullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | B9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportDerivedComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportOrdinaryComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | V6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | N2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | J6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalP1AmbientComposites` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalP1DiagonalTensor` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalTatePullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RawChartScalarCounitPasting` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | Z9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ReductionSiteCoefficientPasting` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ScalarHomPresentationEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.ShriekNormalizedTransitionComparison` | D8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability` | H4 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | A7 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | C8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | Q4 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | F3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerReductionTranspose` | B2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SupportedLatticeHomReductionTower` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TateTwistedProjection` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TowerAdjointCompositorRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | H9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | F8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | unclaimed | Direct textual user; same mathematical statement; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.PoincareDuality.ConstructibleSheafBiduality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | X2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | C8 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | C4 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.Reduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | C9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | K5 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | Y7 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | V1 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | P3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefficientUnitFiniteTor` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CoefficientUnitNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CompletedSystemPullbackPreservation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.DualizingSupportEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionNaturality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemDuality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransitionData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | X3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | Z6 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | Q9 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | D3 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | K5 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionFunctors` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemDualityCompatibility` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralTateLineConstructible` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierModels` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierSignedCalculus` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalDualizingIdentification` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalHomIdentifications` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalOperationsData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierDatum` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierModels` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierUnit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarCompositeModelPasting` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarRefinementClosureSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixCompactSupport` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixCtf` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | F2 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | X5 | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `TargetsCheck` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Additivity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.BaseChangeCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.BorelMoore` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.CoefficientMorphism` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.CompactCohomology` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.CompactPullback` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Correspondence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.CorrespondencePair` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.CurvePieces` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Dualizing` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FibreCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FibreModel` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPoint` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FixedPointScheme` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Frobenius` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.FrobeniusLocalTerm` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.GenericQuotient` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.HomologyUnit` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.KunnethVerdier` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.LefschetzVerdier` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTerm` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.LocalTermLocality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Main` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ModelExtension` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.OpenPieceCoherence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.OpenSquare` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.PointNormalization` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Product` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCompatibility` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ProperCurve` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforward` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ProperPushforwardKernel` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.PullbackFamily` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobenius` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.RelativeFrobeniusIterate` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.ShriekTraceFunctionInduction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Stalk` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.SupportedPairing` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClass` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.TraceClassAdditivity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.WeilBaseChange` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.WeilSheafUpperStar` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.TraceFormula.WeilTrace` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |
| `WeilConjectures.ZetaFunction.WeilObjectComparison` | unclaimed | Transitive importer; same mathematical statement; no adaptation. |

## Status

landed 20261025T164953-L-1147476 2026-10-25 (merge of deliver/Z7/Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction)
