# FrobeniusSquareExchange proof context

## Reason

Prove the normalized rational scalar comparison by localizing its specified integral
isomorphism. Private proved generic tensor and scalar-conjugation helpers keep the
linear and derived constructions folded during proof elaboration. No consumer is adapted.

## Old

The original module began its declarations with this proof context:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
```

Its rational scalar comparison ended with `:= by sorry`. The original public
imports, declaration signatures, data constructions and final global
`attribute [irreducible]` command are preserved verbatim.

## New

The proof-only import is:

```lean
import all Sheaf.Paper.SfScalarExtensionComposition
```

Private proved helpers establish generic tensor functor laws, scalar-conjugation
naturality and localization of the specified integral natural isomorphism.
The finite geometric coefficient binders and helper universes are scoped locally.
The changed proof context includes:

```lean
set_option Elab.async true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
```

After raw localization the Hom map and functor are locally irreducible, and
transparency is respected for subsequent proof elaboration. In `CommonStage`:

```lean
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] operationStageTransitionIso
```

The existing `DerivedPullbackTensorHom` module uses the same local reducibility
setting for this cached category instance. After defining `stageBeta`, it is
locally irreducible. These settings prevent repeated expansion during dependent
endpoint checks. Kernel checking and all original theorem statements remain.
The option `allowUnsafeReducibility` only permits this local reducibility change;
it does not create an unsafe declaration or skip a check. No consumer is adapted.

## Users

`tools/downstream.py Sheaf.Paper.FrobeniusSquareExchange` reports the following transitive
consumers. All retain their statements and meaning; none requires an adaptation.
The holder is the current coordination claim when this record is written.

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged interface. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged interface. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged interface. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged interface. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Unchanged interface. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Unchanged interface. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | W2 | Unchanged interface. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Unchanged interface. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | W3 | Unchanged interface. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Unchanged interface. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Unchanged interface. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged interface. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Unchanged interface. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Unchanged interface. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged interface. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Unchanged interface. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Unchanged interface. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Unchanged interface. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged interface. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | A2 | Unchanged interface. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged interface. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | Q4 | Unchanged interface. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Unchanged interface. |
| Sheaf.Paper.ConstructibleMateCoherence | R1 | Unchanged interface. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Unchanged interface. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged interface. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Unchanged interface. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | Q3 | Unchanged interface. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged interface. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | H5 | Unchanged interface. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | J7 | Unchanged interface. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Unchanged interface. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Unchanged interface. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Unchanged interface. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Unchanged interface. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged interface. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Unchanged interface. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged interface. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Unchanged interface. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Unchanged interface. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Unchanged interface. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Unchanged interface. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Unchanged interface. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Unchanged interface. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Unchanged interface. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Unchanged interface. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Unchanged interface. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Unchanged interface. |
| Sheaf.Paper.PointEquivariantDiagramLift | R6 | Unchanged interface. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Unchanged interface. |
| Sheaf.Paper.PointWeilHeartFlag | J4 | Unchanged interface. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Unchanged interface. |
| Sheaf.Paper.ProjectionFormulaCoherence | Y5 | Unchanged interface. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | P4 | Unchanged interface. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | X6 | Unchanged interface. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Unchanged interface. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Unchanged interface. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Unchanged interface. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Unchanged interface. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged interface. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Unchanged interface. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Unchanged interface. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged interface. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Unchanged interface. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Unchanged interface. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Unchanged interface. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Unchanged interface. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Unchanged interface. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | B9 | Unchanged interface. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged interface. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Unchanged interface. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Unchanged interface. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Unchanged interface. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Unchanged interface. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Unchanged interface. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Unchanged interface. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Unchanged interface. |
| Sheaf.Paper.WeilChosenDualityExchange | D2 | Unchanged interface. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged interface. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged interface. |
| Sheaf.Paper.WfTensorCompletionFrobenius | J3 | Unchanged interface. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Unchanged interface. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | Z6 | Unchanged interface. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Unchanged interface. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Unchanged interface. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Unchanged interface. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged interface. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Unchanged interface. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Unchanged interface. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged interface. |
