# cartier_equality

## Reason

The source and DAG state Cartier equality for a finitely generated field extension.
The old `Algebra.FiniteType k K` assumes finite generation as an algebra; for fields
Zariski's lemma makes this a finite extension and excludes k(t)/k. Replace that
hypothesis with explicit `(⊤ : IntermediateField k K).FG`, as required by the project's
field-generation convention. This strengthens the Lean theorem to the source's full
scope and changes no conclusion. The DAG's natural-language statement was already
correct and is unchanged. No target statement or definition changes.

## Old

```lean
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.FiniteType k K] :
    Module.Finite K (KaehlerDifferential k K) ∧
      Module.Finite K (Algebra.H1Cotangent k K) ∧
      Algebra.trdeg k K + Module.finrank K (Algebra.H1Cotangent k K) =
        Module.finrank K (KaehlerDifferential k K) ∧
      (FiniteDimensional k K →
        Module.finrank K (KaehlerDifferential k K) =
          Module.finrank K (Algebra.H1Cotangent k K))
```

## New

```lean
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    Module.Finite K (KaehlerDifferential k K) ∧
      Module.Finite K (Algebra.H1Cotangent k K) ∧
      Algebra.trdeg k K + Module.finrank K (Algebra.H1Cotangent k K) =
        Module.finrank K (KaehlerDifferential k K) ∧
      (FiniteDimensional k K →
        Module.finrank K (KaehlerDifferential k K) =
          Module.finrank K (Algebra.H1Cotangent k K))
```

## Users

`tools/downstream.py Sheaf.Paper.CartierEquality --uses cartier_equality` finds 223
transitive importers and no application of the declaration outside its own module.
The two direct importers are proof-only imports and both still have their original
proofs. No adaptation is required. Existing finite-type callers, if added later, can
supply `IntermediateField.fg_top k K`; all consumers' mathematical statements stay
identical. Holders below were read from the local claim snapshots.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No declaration use; statements and definitions unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.AdicFieldDifferentialsInjective | D2 | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.GeometricallyRegularH1Injective | E3 | Proof-only importer; no current application of cartier_equality; no adaptation. |
| Sheaf.RingTheory.GeometricallyRegularOverFieldFlat | E3 | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuAppendFlatParameters | C1 | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparation | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparationCore | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuCharPPreparationGlobal | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuEnlargeSolutionModulo | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuFlatCoordinates | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuFlatCoordinatesA0 | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuFlatCoordinatesGivenAdmissible | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuFlatCoordinatesSetup | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuParameterCoefficients | M1 | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuParameterSolution | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.PopescuSolutionModulo | unclaimed | No declaration use; statements and definitions unchanged. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No declaration use; statements and definitions unchanged. |
| TargetsCheck | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration use; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration use; statements and definitions unchanged. |

## Status

landed 20261013T040804-L-3953930 2026-10-13 (merge of deliver/V3/Sheaf.Paper.CartierEquality)
