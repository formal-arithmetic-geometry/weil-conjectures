# AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper

## Reason

The proof adds fully proved private categorical helpers polymorphic in object, Hom
and index universes. Their elaboration also needs the scoped zero-object notation
and the canonical `CategoryTheory.Obj` instances for bundled ring objects. The static
preflight classifies these file commands as a change to what importers see and
requires this administrative record. No public signature or definition changes.
The changes introduce no global instance, notation, attribute or file-level option.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits
```

The two public theorems had the signatures retained in the delivered file; both
proofs were `by sorry`.

## New

```lean
universe u v w u' v'

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Obj
```

The additional universe names are used only by private helpers. The existing public
statements still quantify exactly their original universe `u`. Scoped openings
supply local elaboration instances and notation in this file; no public signature
or data definition is changed. The restriction theorem now has a complete proof;
the coefficient theorem is textually unchanged. The two new imports are proof-only.
Consequently no target meaning changes and no consumer needs adaptation.

## Users

`tools/downstream.py` was started with `--uses proper_image_localizing_proper`.
A separate source-import traversal supplies the complete transitive consumer table
below; direct textual searches find no external use of the theorem name yet. All
existing public signatures are identical, so the effects on these users are empty.
No consumer file is included in this delivery. Holders were read from the project
claim-holder API at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged; no adaptation. |

## Status

landed 20261019T002507-L-2141551 2026-10-19 (merge of deliver/B4/Sheaf.SixFunctors.ProperImageLocalizingProper)
