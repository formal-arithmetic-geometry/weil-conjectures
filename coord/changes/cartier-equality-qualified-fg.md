# cartier_equality

## Reason

Record the requested qualified finite-field-generation notation for upstream review #1428.
The repository already uses the correct `IntermediateField.FG` hypothesis; this edit
changes only its notation, with definitional equality checked by `rfl`. It closes no
proof hole and changes no definition or target meaning.

## Old

```lean
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : IntermediateField.FG (⊤ : IntermediateField k K)) :
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

`tools/downstream.py Sheaf.Paper.CartierEquality --uses cartier_equality` lists
232 downstream modules. Only `Sheaf.RingTheory.PthRootResidueDimensionBalance`
mentions the theorem. Its existing proof is checked against the delivered module;
no adaptation is required. All downstream statements retain exactly their meaning
because the elaborated theorem type and all definitions are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.AdicFieldDifferentialsInjective | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.ClosedFiberDefectDerivationExtension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.ClosedFiberDerivationExtension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.DifferentialCoordinatesCotangentIndependent | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FiniteTypeGRing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FiniteTypeGRingAux | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FiniteTypeIntGRing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FormallySmoothAdicLift | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiberComplete | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FormallySmoothCompleteLocalGenericFiber | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FormallySmoothCompleteLocalRegular | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FsAdicClosedFiberModel | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.FsAdicLiftOverFiniteCoefficientMap | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.GeometricallyRegularDifferentialFamily | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.GeometricallyRegularH1Injective | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.GeometricallyRegularOverFieldFlat | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.ModelOfResidueSmooth | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PolynomialFormalFiber | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PolynomialFormalFiberGeometric | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PolynomialGRingComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuAppendFlatParameters | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuCharPPreparation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuCharPPreparationCore | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuCharPPreparationGlobal | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuEnlargeSolutionModulo | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuFlatCoordinates | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuFlatCoordinatesA0 | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuFlatCoordinatesGivenAdmissible | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuFlatCoordinatesSetup | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuInitialFlatCoordinates | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuParameterCoefficientModel | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuParameterCoefficients | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuParameterSolution | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PopescuSolutionModulo | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PowerSeriesParameterMapFormallySmoothAdic | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| Sheaf.RingTheory.PthRootResidueDimensionBalance | unclaimed | Same elaborated hypothesis; existing `IntermediateField.fg_top` argument still applies. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| TargetsCheck | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No semantic change: only definitionally identical notation in an imported theorem. |

## Status

landed 20261013T215617-L-903582 2026-10-13 (merge of deliver/Y3/Sheaf.Paper.CartierEquality)
