# finiteClassicalUnboundedComparison proof context

## Reason

The completed proof uses additional category-theory namespaces, zero-object notation,
and elaboration options. The static interface checker records these top-level commands
as an interface change. These commands configure elaboration within this module. Every
public import, declaration signature, universe and visibility stays identical. All added
helpers are private and fully proved; no new public instance or attribute is introduced.
No definition used by a target changes, so no target meaning changes.

The direct proof import of ProEtaleSiteComparison is retained because the delivery gate
marks it as part of the unit route. The proof follows that comparison throughout.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open scoped ZeroObject
```

## Users

All transitive importers returned by tools/downstream.py are listed below. The only
consumer mentioning finiteClassicalUnboundedComparison is UnboundedSiteComparison:
its unchanged application supplies exactly the original arguments and uses the same
three conjunction clauses. No consumer is adapted. Module-local open commands and
elaboration options do not change exported names, instances, definitions or statements;
thus the other importers receive exactly the same mathematical interface. Holders are
read from the current claim records; no claim is taken or modified.

The exact delivered module and unchanged UnboundedSiteComparison were compiled together
through lcompile.py in an isolated scratchpad overlay. Both compiled cleanly; no consumer
source was edited. The separate final single-file compile also passed without warnings.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | V7; not adapted | Same exported interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5; not adapted | Same exported interface; no adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | R1; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | N3; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | N1; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | R2; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | M3; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | V7; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | V9; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | R5; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | X9; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | N4; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | H1; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | F8; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | D9; not adapted | Same exported interface; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Q8; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | T8; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | P4; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | G6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | K1; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4; not adapted | Same exported interface; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1; not adapted | Same exported interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed; not adapted | Same exported interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed; not adapted | Same exported interface; no adaptation. |
| TargetsCheck | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.Statement | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed; not adapted | Same exported interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed; not adapted | Same exported interface; no adaptation. |

## Status

landed 20261020T122132-L-483046 2026-10-20 (merge of deliver/S3/Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison)
