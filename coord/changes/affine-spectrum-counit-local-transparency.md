# AlgebraicGeometry.affineSpectrum_counit_compatibility

## Reason

The static delivery checker conservatively treats a new `attribute` command as an
interface change. The command is `attribute [local irreducible] derivedPullback`,
inside this module's namespace. It keeps the large derived-pullback existence
construction folded during elaboration of the spectrum coordinate calculation.
The namespace closes at the end of the file, restoring transparency; importers
receive no change to `derivedPullback`. There is no changed definition or theorem
signature and no target meaning changes. No downstream adaptation is required.
The local compile improved from 58.0 seconds to 48.6 seconds; both proofs compiled.

## Old

The file used these elaboration settings and no local irreducibility override:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The existing theorem signature was:

```lean
theorem affineSpectrum_counit_compatibility
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (K : schemeDerivedCategory X) :
  (derivedPullback f).map ((affineSpectrumDerivedDirectImageIso f).hom.app K) ≫
      (affineSpectrumForwardPullbackIso f).hom.app
        ((schemeDerivedDirectImage (Spec.map f.appTop)).obj
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      (derivedPullback X.toSpecΓ).map
        ((canonicalSchemeDerivedAdjunction (Spec.map f.appTop)).counit.app
          ((derivedPullback X.isoSpec.inv).obj K)) ≫
      affineSpectrumUnitInv X K =
    (canonicalSchemeDerivedAdjunction f).counit.app K
```

## New

The theorem signature is identical to the Old section. The elaboration settings are:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

These settings affect elaboration in this file and do not change imported declarations.
The structural-component simplification briefly restores the first option to `false`
inside its proof. The namespace also includes:

```lean
attribute [local irreducible] derivedPullback
```

Only elaboration of this module uses that local attribute. Its mathematical data,
functors, comparison maps and adjunction choices remain identical.

## Users

The table lists every downstream module reported by `tools/downstream.py`.
The only direct theorem user is `Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility`,
whose theorem application still has exactly the same type. Every other row is a
transitive importer. No row needs an adaptation because the change is local and
all existing declaration signatures are identical.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpectrumBaseChangeComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | C1 | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenAffine | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| TargetsCheck | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unaffected: local transparency only; signature and definition unchanged. |

## Status

landed 20261013T201802-L-3974095 2026-10-13 (merge of deliver/M3/Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility)
