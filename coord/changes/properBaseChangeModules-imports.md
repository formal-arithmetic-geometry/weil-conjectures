# AlgebraicGeometry.Etale.properBaseChangeModules imports

## Reason

The theorem is now proved using the existing coefficient-forgetting theorem and
bounded-below abelian proper base change. The separate module-cohomology-conventions
import is unused. Proof dependencies should be private; public imports should expose
the definitions and instances used by the unchanged theorem signature. This record
covers the import-interface cleanup; no declaration signature or definition changes.

## Old

```lean
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
public import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
```

The signature beginning `theorem properBaseChangeModules (Λ : Type (u + 1))`
is unchanged in full. No target statement or definition is changed and no target
meaning is changed. The canonical comparison definitions remain publicly visible
through their own module. The old direct `Derived` import is redundant through that
module. The two proved facts used only by the proof are private imports.

## Users

The theorem's complete signature and all definitions are unchanged. The five direct
consumers are checked from their unchanged current sources against the revised item
in `scratchpad/consumer-check` through `lcompile.py --all`. They are not delivered
or adapted. No target statement or meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProperBaseChangeModules | X2 | Proof completed; imports narrowed. |
| Sheaf.AlgebraicGeometry.BirationalBadLocusComparison | not adapted | Direct consumer; unchanged source checked. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberOpenImmersionSheafFiniteness | not adapted | Direct consumer; unchanged source checked. |
| Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk | not adapted | Direct consumer; unchanged source checked. |
| Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude | not adapted | Direct consumer; unchanged source checked. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPurityObjects | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ArithmeticRoots | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CompactificationLocalizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.DualizingObjectPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteProperBaseChange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteProperLocalizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteTorStability | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.FourierTraceFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralProperBaseChange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.IntegralProperProjectionFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.InterchangeProperPasting | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.MateOpenRestriction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.NearbySpecializationSlice | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.OrientedProperFibreExchange | not adapted | Direct consumer; unchanged source checked. |
| Sheaf.Paper.OrientedProperImageConstructibility | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperHeartBound | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.PurAdicReconstruction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.PurityDncInvariance | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalPurityPresentation | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.RestrictionLocal | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.SfBidualityClass | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.SmoothPurityMap | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.SmoothTrace | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.TraceBaseChangeSecond | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.VerdierExchange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.WeilFourierInversion | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.WeilOne | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Paper.ZlShriekComposition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.FiniteDualizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.RationalOperations | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SixFunctors.RationalVerdier | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Targets.PoincareUncurry | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.Targets.SmoothPurityQbar | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | not adapted | Indirect consumer; signatures and definitions unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | Indirect consumer; signatures and definitions unchanged. |
| TargetsCheck | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.Poincare | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.Verdier | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.SmoothPurity.Defs | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.Statement | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Basic | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Statement | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Curve | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LFunction | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Rationality | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Indirect consumer; signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Indirect consumer; signatures and definitions unchanged. |

The table is the full current `tools/downstream.py --uses` result. No module other
than the item is edited, so there are no forced adaptations and no change to any
held module. All transitive consumers retain the same theorem and definitions;
the maintainer's global build verifies the complete import closure.

## Status

landed 20261019T034345-L-424955 2026-10-19 (merge of deliver/X2/Sheaf.SixFunctors.ProperBaseChangeModules)
