# finiteTorOrdinaryPullComplete_fixed_datum

## Reason

Withdraw an unsupported generalization and replace its actual consumer's proof.
STATEMENT-DISPUTED: the fixed-datum and unrestricted lemmas claim preservation of
arbitrary derived-complete inputs by ordinary pullback, although exact inverse image
need not preserve infinite products. Their sources do not state this assertion.
Bhatt--Scholze Remark 6.5.10 gives ordinary/completed pullback agreement for finite
compositions of qcqs weakly etale maps and constructible closed immersions. Stacks
099N(5), proetale.tex lemma-pushforward-Noetherian-case, concerns COMPLETED pullback.
Neither supplies the claimed product transport for arbitrary finite-type morphisms.
No counterexample in the exact Lean encoding is asserted here; the withdrawal removes
an unsupported proof route and replaces every use while preserving the required parent.

The retained theorem has finite-Tor constructible inputs (or the coefficient unit).
Its proof now constructs source projective charts, transports the explicit chart
models, proves the bounded models complete, transports this fact by their specified
isomorphisms, and descends on the finite trees and affine opens. Thus the parent
statement stays exactly as before. No target, definition, instance, or public import
of a retained module changes.

## Old

```lean
theorem finiteTorOrdinaryPullComplete_fixed_datum
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hs : IsSeparated f) (_ht : LocallyOfFiniteType f) (_hq : QuasiCompact f)
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : IsDerivedComplete l E Y D hl K) :
    IsDerivedComplete l E X D hl
      ((IntegralSystemRealization.ringedPull l E f).obj K)

theorem finiteTorOrdinaryPullComplete_of_complete {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hs : IsSeparated f) (_ht : LocallyOfFiniteType f) (_hq : QuasiCompact f)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : IntegralOnSlice.IsComplete l E Y none K) :
    IntegralOnSlice.IsComplete l E X none
      ((IntegralSystemRealization.ringedPull l E f).obj K)

```

The old parent proof discarded the finite-Tor hypothesis except for source
completeness, and applied finiteTorOrdinaryPullComplete_of_complete to both cases.

## New

The two declarations above are withdrawn through deleted.txt; their DAG nodes remain,
with lean set to null and the obsolete proof dependencies removed. The assigned
module's only parent is the unrestricted lemma; that lemma's only consumer is the
retained finiteTorOrdinaryPullComplete, whose statement and public imports are
verbatim. Its replacement proof depends on these explicit steps:

1. finiteTorAffineProjectiveCharts, applied to K twice, provides source charts.
2. finiteTorPullbackAffineProjectiveCharts transports the supplied charts (or the
   regular coefficient unit) to ordinary pullback. This is the one new theorem hole.
3. boundedProjectiveComplex_complete proves the resulting model complete.
4. canonicalCompletionUnitCriterion and naturality transport completeness across
   the model isomorphism, cancelling the image of its invertible map.
5. affineTreeCompleteDetection descends chartwise completeness to X.

The new geometry lemma assumes concrete bounded finite-free-retract models on the
source, not source completeness. Its conclusion supplies models and splittings,
not completeness. The parent combines it with two independent existing theorems;
this is not the original statement with a renamed predicate or witness.

## Users

The read-only downstream queries for both withdrawn modules and the retained parent
listed the following transitive users. All declarations and public imports of the
retained parent are identical. Private proof imports of the withdrawn modules were
never reexports, so transitive users retain their interfaces. The only uses of the
withdrawn declarations are in the two files explicitly repaired or withdrawn below.
The original source checkout and quarantined node records were searched for additional
references; no additional parent of the assigned node was found. The unit record
sk-thm-sf-compatibility has no realized step attached to either withdrawn node.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | P8 | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportProjectionFormula | H3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportScalarGammaIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | E4 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | J4 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactificationBProjectionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactificationBProjectionDomains | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompactificationBProjectionReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositeProjectionCoefficients | S6 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CompositionTensorMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedCompositorRealization | G3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | C4 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | K3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteForwardProductCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionCompactificationSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionCompactificationTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionCompositionTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionFromDescent | K5 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | T9 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteRefinementAmbientNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteRefinementProjectionRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralSupportReductionNormalization | D5 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | C7 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilComparisonStructure | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | V9 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionFormulaCoherence | E3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityKappaStages | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityTateDatum | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalSmoothPurityCanonical | N4 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | F9 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | C3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.StrictProperRestrictionComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.StrictScalarTowerAssociator | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemTensorPresentationData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.SystemTensorSemilinearRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerGeometricPurityAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerGeometricPurityData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerGeometricPurityMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerIsomorphismPullback | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerOrientationEvaluation | X8 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerPurityPresentationRetagging | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerSemilinearPurityFactors | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTensorPresentationRetagging | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TransportIntegralCounitData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TransportIntegralCounitRealization | J3 | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientExactClopenData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientSystemBetaLocalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientSystemClopenLocalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CanonicalShiftSynchronization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | F5 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | A4 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete | unclaimed | Proof and private imports replaced; signature and public imports verbatim. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteFixedDatum | H8 | Withdrawn unsupported declaration; all direct consumers repaired in this packet. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteOfComplete | unclaimed | Withdrawn unsupported declaration; all direct consumers repaired in this packet. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralBasicGeneratorSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCanonicalRealizationSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionCanonicalEquations | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionCanonicalSupport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionRecursionData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralExpressionTransposeIsIso | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOpenRealizationNaturality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare | B5 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares | B7 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares | B9 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare | C5 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.IntegralSupportCounitProjection | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OrdinaryAmbientAlphaPasting | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OrdinaryAmbientAlphaUnits | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.PrimitiveCompletionEffectivity | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | U1 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.PublishedSystemAmbientCoherence | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.PublishedSystemTensorComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | B3 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RefinementProjectionLocalTensor | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RefinementProjectionProperComposition | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.RefinementProjectionWords | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | G4 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | C3 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | C2 | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Unchanged; retained parent interface identical. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged; retained parent interface identical. |
| TargetsCheck | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.Statement | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.VerdierDual | C4 | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged; retained parent interface identical. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged; retained parent interface identical. |

Validation: the new chart statement, replacement parent, and both original direct
importers of that parent compiled with lcompile. The RationalSmoothPurityCanonical
check initially exceeded the limit; after profiler diagnostics were removed its
final clean check passed. Published and overlay probes have the same retained
theorem-type hash and relevant instance registrations. No consumer edit is included.

## Status

landed 20261027T050609-L-242600 2026-10-27 (merge of deliver/H8/Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteFixedDatum)
