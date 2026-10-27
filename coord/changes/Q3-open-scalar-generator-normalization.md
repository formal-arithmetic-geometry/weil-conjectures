# WeilConjectures.OpenTensorQuotient.ScalarCompatibility

## Reason

The record is documented as the actual normalized scalar comparison but omitted its
identity-on-extension-summands equation. The former fields allow negating both finite and
systems isomorphisms. Their evaluation equation remains true, and negating r retains
ScalarComparison.components, whereas the scalar unit composite changes sign. For j = id,
l = 3, E = Q_3 and a nonzero module in degree zero over a point, the quotient unit is
not its negative. Thus the old arbitrary-sc unit theorem is false.

Add the coefficient-independent finite generator equation, not a hypothesis containing
the desired unit equation. It is the literal identity on summands from Stacks 03DI/03DA
and 0E8I, already promised by openQuotientScalarCompatibilityData and its proof docstring.
That existing existence hole becomes stronger and remains open; this is reported explicitly.
The unit theorem then follows from tc.generators by genuine extension/sheafification
extensionality. Completed coefficients, quotients, functors, adjunctions and strict
transition maps do not change. The target statements and the unit route stay fixed.

Live server inspection found OpenTensorQuotientData unclaimed; only this module and
Q3's item are edited. No source-library module is edited. No other module constructs
ScalarCompatibility: users project its existing fields or receive it from the existing
existence theorem. All nine direct importers are checked, one file at a time.

## Old

```lean
structure ScalarCompatibility where
  finite : ∀ n : ℕ,
    IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o
  systems : (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
      forgetSystems l E X ≅ forgetSystems l E U ⋙ extendTower l E j o
  evaluation : ∀ (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
    (n : ℕ) (i : ℤ),
    HEq (((systems.hom.app C).app (op n)).f i)
      ((finite n).hom.app ((coefficientSequenceEvaluation l E U n).obj (C.X i)))
```

## New

```lean
structure ScalarCompatibility where
  finite : ∀ n : ℕ,
    IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o
  sections : ∀ (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
    ((finite n).hom.app M).val.app (op V)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
    IntegralOpenReduction.extensionSection l E j o
      ((scalarReductionRestriction l E U n).obj M) V a x
  systems : (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
      forgetSystems l E X ≅ forgetSystems l E U ⋙ extendTower l E j o
  evaluation : ∀ (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
    (n : ℕ) (i : ℤ),
    HEq (((systems.hom.app C).app (op n)).f i)
      ((finite n).hom.app ((coefficientSequenceEvaluation l E U n).obj (C.X i)))
```

## Users

Generated from tools/downstream.py Sheaf.SixFunctors.OpenTensorQuotientData --uses
WeilConjectures.OpenTensorQuotient.ScalarCompatibility. The six textual declaration
users (including the defining module) were inspected; the table also retains all graph
importers. The defining module is unclaimed on the live server and is repaired here.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed on live server | Add missing generator normalization; other declarations unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationCoordinates | K4 | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | K2 | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | F1 | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionFiniteEvaluation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionOpenFactorReduction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionProperFactorReduction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionSupportEvaluation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionSupportFactorCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionSystemNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperSupportReductionIdentity | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralSupportReductionNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | J3 | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementTransposeRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorOpenRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorProjectionRealization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorQuotientRealization | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData | unclaimed in shared snapshot | Existing sorry now requires the promised generator normalization; no new sorry or source edit. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenTensorQuotientCoefficientComparisons | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenTensorQuotientRoosNormalization | unclaimed in shared snapshot | Direct importer; compile against repaired structure; no ScalarCompatibility constructor to adapt. |
| Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility | Q3 | Prove scalar-unit equation using new sections field; keep existing signatures. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in shared snapshot | Indirect importer; retained projections and all other definitions unchanged; no adaptation. |

## Status

landed 20261027T210203-L-1668970 2026-10-27 (merge of deliver/Q3/Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility)
