# Etale open-exchange proof elaboration commands

## Reason

The proof needs private mate lemmas and local irreducibility annotations to avoid unfolding
large sheaf and derived-functor constructions. The interface checker conservatively counts
changes to commands, including `attribute [local irreducible]`, as interface changes.
These attributes have local scope and do not modify exported definitions or theorem types.
The new tower and source-open modules supply separate intermediate results.

## Old

The assigned module has no local transparency annotations or private mate helpers before
`openExchange_adjunct`. Its proof is `by sorry`. The definitions `openExchangeIso` and
`canonicalCompactSupportExchange` and the theorem signature are as in the shared source.

## New

The added local transparency command is verbatim:

```lean
attribute [local irreducible] lowerStar openImmersionLowerShriek upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
```

The remaining added commands are namespaces and options scoped to private proved helpers or
to the assigned proof (`set_option maxRecDepth 10000 in`). All existing declaration
signatures and both definition bodies are unchanged. The local annotation affects only
elaboration in this file. No downstream adaptation is needed and no target meaning changes.

## Users

`tools/downstream.py` lists the following transitive consumers. A textual search for
`openExchange_adjunct` finds only the assigned module itself, held by B6; that proof is
completed in this packet. All consumers retain their signatures, definitions and imports.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | C6 | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.PunctualPurityProperDegreeDescent` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.PunctualPurityTraitTest` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.DeligneLaumon.GenericDualityModel` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | W8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPurityRootComparisons` | X5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPuritySourceReduction` | X6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicPurityTwistReduction` | X8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.ChernFlagFormula` | G4 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | A4 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.EtaleSectionDeformationComparison` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | F3 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | U5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | K8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | T6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | S7 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteReductionComparisons` | T7 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteReductionRootCharts` | D8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteRegularReductionDualizing` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | G9 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | A4 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | W2 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | V6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | W4 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.GlobalVerdierDuality` | R5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.LocalizedTopChern` | E5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.NoetherianPrimePowerSmoothDuality` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.PurAdicReconstruction` | H8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | G3 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | G6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | K8 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.SfBidualityClass` | C6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.SmoothPurityMap` | R2 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.TwistFrobeniusScalar` | G4 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.VectorBundlePurity` | S1 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.WeilFourierInversion` | J6 | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.WeilOne` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | E2 | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | D6 | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | E6 | Unaffected; local proof elaboration only. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | A9 | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | R5 | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | A4 | Unaffected; local proof elaboration only. |
| `Sheaf.SixFunctors.RationalVerdier` | V4 | Unaffected; local proof elaboration only. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Unaffected; local proof elaboration only. |
| `Sheaf.Targets.VectorBundlePurity` | F6 | Unaffected; local proof elaboration only. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unaffected; local proof elaboration only. |
| `TargetsCheck` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.Statement` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Unaffected; local proof elaboration only. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Unaffected; local proof elaboration only. |

## Status

landed 20261020T051026-L-1534117 2026-10-20 (merge of deliver/B6/Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint)
