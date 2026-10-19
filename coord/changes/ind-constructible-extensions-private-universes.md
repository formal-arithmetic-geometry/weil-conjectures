# IndConstructibleExtensions private-helper universes

## Reason

The proof adds three proved private helpers, generic in the ambient category's object
universe. The static interface checker treats adding the universe name `w` to the
existing universe command as a command-interface change. This record documents that
source change. Neither existing public theorem gains a universe parameter: its complete
signature, including `Scheme.{u}` and `ObjectProperty.ind.{u + 1}`, is unchanged.
The added name scopes only the private helpers. All public imports are unchanged, and
all added proof imports are non-public. No existing definition or statement is repaired
or weakened. The target statements and their interpretations are unchanged.

## Old

```lean
universe u
```

## New

```lean
universe u w
```

## Users

The table lists the complete transitive downstream set reported by
`tools/downstream.py Sheaf.Paper.IndConstructibleExtensions --uses
indConstructible_of_shortExact indConstructible_of_shortExact_padicAlgCl`.
The only external source that names these declarations is
`Sheaf.Paper.AmbientIndDerivedTriangulated`, lines 184 and 186; its applications are
unchanged because both existing signatures are identical. Universe-name commands
introduce declaration-local parameters, and the extra name is used only in private
helper declarations. Thus no downstream statement or definition changes meaning and
no downstream source needs adaptation. Holders below are the current claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IndConstructibleExtensions | K4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| TargetsCheck | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.Statement | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No change to existing signatures, visibility, definitions or imports seen by consumers; no adaptation. |

## Status

landed 20261019T005313-L-2750797 2026-10-19 (merge of deliver/K4/Sheaf.Paper.IndConstructibleExtensions)
