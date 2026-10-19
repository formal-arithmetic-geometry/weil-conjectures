# DiscreteNoetherianConstructibleSerre public imports

## Reason

The completed étale proof and both public signatures do not use the finite-ring
realization interface or the generic small-site finite-type predicate. Remove their
public imports as unused dependencies. No public declaration changes type or meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
```

## New

Both public import lines are removed. The proved private helpers are enclosed in
`namespace Scheme` with `open Opposite`; the namespace closes before the original
public declarations. This local name-resolution command changes no public signature.
All other public imports and both public theorem signatures are unchanged. Proof-only imports of KernelCokernel and OpenClosed supply
the concrete étale argument; all new declarations are private.

## Users

Source import-graph inventory, refreshed 2026-10-19. No consumer is edited in this
delivery. Public-import removal changes name availability. All six direct consumers compiled
successfully against the delivered module via lcompile.py on 2026-10-19, without
warnings or edits (3.1 to 5.3 seconds each); the delivered module compiled in 10.4 seconds.
No downstream public signature changes, and all direct imports of this item are proof
imports, so its removed reexports were not exposed further through these consumers.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | X2 | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | C8 | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | D4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | H9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicClosedConstructible` | unclaimed | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.AdicStratifiedPerfect` | P5 | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | Q2 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.BoundedConstructibleHomFiniteness` | H5 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | T6 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | M1 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CoefficientChangeDualizing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | R4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CompactificationLocalizing` | F4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | T9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ConstructibleFiniteTorAdjunctions` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.DetThmSfCtfStabilityInternalHom` | unclaimed | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | V5 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | Y8 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | U1 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | U2 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | U3 | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | Q7 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FiniteTorInternalHomAnyField` | unclaimed | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | V4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralConstantModelHeartClosure` | H7 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | R8 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | W9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.InterchangeProperPasting` | S4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | J5 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | A4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.MateOpenRestriction` | D7 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | B3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.PrimeFieldTensorDevissage` | unclaimed | Direct proof importer; signatures unchanged; check reduced reexports. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | X6 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ProperExceptionalRestriction` | P2 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.PurityDncInvariance` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RationalExceptionalRestriction` | K8 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | U4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RationalRestrictionGlue` | R9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.RestrictionLocal` | R3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.TraceBaseChangeSecond` | E4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | K3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.WeilOne` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | F1 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | F3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | Z9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | G3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | M7 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | N4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | T2 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | U3 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | G9 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | B4 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | U1 | Transitive consumer; no declaration signature changes. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Transitive consumer; no declaration signature changes. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Transitive consumer; no declaration signature changes. |
| `TargetsCheck` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.Statement` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Transitive consumer; no declaration signature changes. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Transitive consumer; no declaration signature changes. |

## Status

landed 20261019T002457-L-2139180 2026-10-19 (merge of deliver/A5/Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre)
