# ModuleCat.augmented_lift_homotopy

## Reason

Repair the returned delivery's duplicate proof of the same augmented lifting theorem.
`Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy` is unclaimed. Under
the 2026-10-14 rule allowing an unclaimed module to be changed like a held one, this
interface change is reviewed in its original module. It is not a forced adaptation
of another group's held module. Remove
`private` from its existing generic helper and document it. The theorem's binders,
conclusion, universes and complete proof body stay identical. The item's proof imports
and uses it instead of proving the theorem again. The duplicate `prevD_chain` in the
item is removed in favor of Mathlib's `Homotopy.prevD_chainComplex`.

## Old

```lean
private theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (K : ChainComplex D ℕ) (π : K.X 0 ⟶ N)
    (hz : K.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (K.d 1 0) π hz).Exact)
    (hsucc : ∀ n : ℕ,
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ K) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a')
```

## New

```lean
theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (K : ChainComplex D ℕ) (π : K.X 0 ⟶ N)
    (hz : K.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (K.d 1 0) π hz).Exact)
    (hsucc : ∀ n : ℕ,
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ K) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a')
```

The helper is now public in the existing `@[expose] public section`. Its proof is
unchanged. No previously public declaration, definition or target signature changes.
No other module requires adaptation. The generic helper has its own DAG node,
`new-t4-augmented-resolution-lift-homotopy`, attached to its verbatim signature in
this existing module. The quotient homotopy node attaches only its quotient theorem
and cites the generic helper in its proof. This corrects reviewer X-fe77b's C3/C4
metadata finding without changing any Lean signature or proof body.

## Users

The source-only downstream scan found 425 transitive dependents. Searching all
of them for `augmented_lift_homotopy` found no user outside its defining module.
All existing public API types and definitions are identical. Each current downstream
module is listed below; none needs an edit. The item is the new consumer. Holders are
from the local claim snapshot read during this repair.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy` | unclaimed | Expose its existing augmented homotopy theorem; proof unchanged. |
| `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates` | T4 | Import and apply the shared theorem. |
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetCoefficientNaturality` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ClosedCoefficientSourceTransitionIso` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ClosedCoefficientTargetTransitionIso` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedSelfTorAffineCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.DivisorClassCurve` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.DivisorPicRepresentative` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleOpenInjectiveLerayEdge` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenericComponentsSplit` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GenusInvariant` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianClopenRestriction` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardSurjective` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheafNonnegative` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtExterior` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparisonFactorization` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicity` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericClopen` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorAmbientLocalizedComparisons` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorAmbientResolutionCharts` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorAmbientSectionCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorAugmentedResolutionCharts` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorChartSquareDualization` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorChosenResolutionCharts` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChart` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorNonpositiveChosenComparisons` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorNonpositiveFlatSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorOrdinaryResolutionSections` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorTargetBasicLocalization` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SelfTorTargetRestrictionCoordinates` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.SteinFactorizationAffine` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.Paper.GaloisLisseRepresentations` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No use of the formerly private helper; unchanged. |
| `Sheaf.Paper.ZariskiH0ProperHenselianPair` | unclaimed | No use of the formerly private helper; unchanged. |
| `TargetsCheck` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Picard` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.Scheme` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Cancellation` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Dualizing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Localization` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Point` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Shift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Triangulated` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | XRdbb7091a3d1839f4 | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Basic` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Duality` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtension` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing` | unclaimed | No use of the formerly private helper; unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward` | unclaimed | No use of the formerly private helper; unchanged. |

## Status

landed 20261015T034824-L-298475 2026-10-15 (merge of deliver/T4/Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates)
