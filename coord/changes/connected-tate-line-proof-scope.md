# AlgebraicGeometry.Scheme.connected_tate_line_endomorphisms

## Reason

A theorem-scoped `attribute [local irreducible] shiftedFiniteEtaleTateLine in`
prevents expensive unfolding during elaboration of the proof. The attribute ends
with this theorem. The definition, existing declaration signatures, visibility,
instances and public imports are unchanged. No target statement changes.
The checker conservatively treats the scoped command as an interface change.

## Old

The existing signature, verbatim (no scoped attribute):

```lean
theorem connected_tate_line_endomorphisms
    (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : 0 < N) (hInvertible : IsUnit (N : k))
    (B : Type (u + 1)) [CommRing B] (hB : (N : B) = 0)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] [ConnectedSpace Y] (r : ℕ) (d : ℤ) :
    Function.Bijective
      (fun b : B => b • 𝟙 (shiftedFiniteEtaleTateLine B N Y hB r d)) ∧
    (∀ (G : Etale.DerivedCategoryModule B Y ⥤
        Etale.DerivedCategoryModule B (Spec (.of k))) [G.Linear B],
      Nonempty (G.obj (shiftedFiniteEtaleTateLine B N Y hB r d) ≅
        Etale.constantComplex B (Spec (.of k))) →
      ∀ v : shiftedFiniteEtaleTateLine B N Y hB r d ⟶
          shiftedFiniteEtaleTateLine B N Y hB r d,
        IsIso (G.map v) → IsIso v)
```

## New

The same signature, verbatim, under a theorem-local attribute:

```lean
attribute [local irreducible] shiftedFiniteEtaleTateLine in
theorem connected_tate_line_endomorphisms
    (k : Type u) [Field k] [IsAlgClosed k]
    (N : ℕ) (hN : 0 < N) (hInvertible : IsUnit (N : k))
    (B : Type (u + 1)) [CommRing B] (hB : (N : B) = 0)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] [ConnectedSpace Y] (r : ℕ) (d : ℤ) :
    Function.Bijective
      (fun b : B => b • 𝟙 (shiftedFiniteEtaleTateLine B N Y hB r d)) ∧
    (∀ (G : Etale.DerivedCategoryModule B Y ⥤
        Etale.DerivedCategoryModule B (Spec (.of k))) [G.Linear B],
      Nonempty (G.obj (shiftedFiniteEtaleTateLine B N Y hB r d) ≅
        Etale.constantComplex B (Spec (.of k))) →
      ∀ v : shiftedFiniteEtaleTateLine B N Y hB r d ⟶
          shiftedFiniteEtaleTateLine B N Y hB r d,
        IsIso (G.map v) → IsIso v)
```

The existing docstring between the attribute and theorem stays unchanged.
`shiftedFiniteEtaleTateLine` itself is textually unchanged.

## Users

`tools/downstream.py Sheaf.Paper.ConnectedTateLineEndomorphisms
--uses shiftedFiniteEtaleTateLine` lists 195 downstream modules and finds the
name only in the item itself. The table includes the item and every downstream
module, with current holders read from claim records. No consumer sees the local
attribute, so no adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.DeligneLaumon.GenericDualityModel` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.Composition` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalCoherence` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalComposition` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalProjection` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.AdicExceptionalScalars` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | A4 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ConnectedTateLineEndomorphisms` | G3 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | U5 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | K8 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteRegularReductionDualizing` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | W4 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | K8 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | W5 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | C6 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | X2 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | J6 | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | A9 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | J1 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | F2 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | J5 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | E3 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | M6 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Same exported signature and definition; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | V4 | Same exported signature and definition; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Same exported signature and definition; no adaptation. |
| `TargetsCheck` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Adic.Reduction` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRange` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.CohomologicalRangeAffine` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.CurveTopCohomology` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.EulerProduct` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierStalk` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LissePoincarePairing` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.OpenClosedTriangle` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDual` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualFinite` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.WeilSheaf.VerdierDualLocalization` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same exported signature and definition; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same exported signature and definition; no adaptation. |

## Status

landed 20261019T154010-L-3025614 2026-10-19 (merge of deliver/G3/Sheaf.Paper.ConnectedTateLineEndomorphisms)
