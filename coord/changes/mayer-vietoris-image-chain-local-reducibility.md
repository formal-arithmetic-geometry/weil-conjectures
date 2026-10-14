# AlgebraicGeometry.schemeMV_image_chain_squares

## Reason

Repair of return H10 (reviewer X-7f5b9): the returned full file exceeded 60 seconds.
Declaration-boundary profiling found about 13 seconds in the ordinary unit proof,
7 seconds in ordinary nested restriction, 8 seconds in the complex unit proof,
and 28 seconds in complex nested restriction, before the public proof even began.
The previous irreducibility block protected only the final proof. Move protection
of the ordinary constructions to the beginning, respect transparency by default,
and specify the degreewise naturality equation explicitly. The final difference
calculation is proved with abstract categories in a private proved helper and then
instantiated, avoiding concrete sectionwise unfolding during additive rewriting.
The repaired complete file compiled cleanly in 49.0 seconds locally.

All definitions, existing signatures, visibility and public imports are unchanged.
All overrides are local. No downstream adaptations or target reviews are needed.
This record is required by the static preflight for local attribute commands.

## Old

The returned module set:

```lean
set_option backward.isDefEq.respectTransparency false
```

After its degreewise helpers it added:

```lean
attribute [local irreducible] schemeMVImageComponent schemeMVImageIso
  schemeOpenModuleImageComplexRestriction
```

The repository baseline has neither irreducibility block. The local instance
priority command is kept unchanged.

## New

The module defaults to:

```lean
set_option backward.isDefEq.respectTransparency true
```

Before the proved helpers:

```lean
attribute [local irreducible] schemeMVImageIso schemeOpenModuleImageRestriction
  schemeMVUnderivedOpenRestriction schemeMVUnderivedOpenComposition
  schemeOpenModuleAdjunction schemeOpenRestrictionCompIso
```

After the degreewise helpers:

```lean
attribute [local irreducible] schemeMVImageComponent
  schemeOpenModuleImageComplexRestriction
```

Transparency is relaxed only for the final instantiation of the abstract
calculation (including the definitional inverse-image/intersection identification).
This setting changes elaboration only and is not exported.

## Second-reading proof simplification

The second reader replaced the ordinary adjunction and cancellation arguments
with the existing ordinary comparison unit and restriction lemmas, after proving
that their comparison equals `schemeMVImageIso`. The degreewise and abstract
additive arguments remain. The full revised module compiled in 39.7 seconds.
The local attribute commands above are retained and still affect no downstream
interface, signature, definition, or public import. The ordinary comparison
module is a plain proof-only import. No forced adaptations are required.

## Users

The following is the complete transitive downstream list from
`tools/downstream.py Sheaf.AlgebraicGeometry.MayerVietorisImageChainSquares --names`.
Holder names are the claim-file snapshot when this record was written. Only
`Sheaf.AlgebraicGeometry.MayerVietorisImageChainMap` directly mentions the public
theorem. No downstream module requires adaptation, since local attributes do not
export and the theorem's signature and all public imports are identical.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | Y3 | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.CartesianTensorDataComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | K2 | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisDirectImageBoundary` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DivisorClassCurve` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.DivisorPicRepresentative` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenericComponentsSplit` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GenusInvariant` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianClopenRestriction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardSurjective` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.MayerVietorisImageChainMap` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.NoetherianApproximationData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectComplexDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms` | R3 | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore` | S4 | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1IntersectionSection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosed` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardProductOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardProductOpenData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality` | H3 | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMVConePresentation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMVSESPresentation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMayerVietoris` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericClopen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SingleComplexOpenUnion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.SteinFactorizationAffine` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentSections` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.Paper.GaloisLisseRepresentations` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `Sheaf.Paper.ZariskiH0ProperHenselianPair` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `TargetsCheck` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Picard` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.Scheme` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.AlgebraicGeometry.TheoremOfCube` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No effect: local attributes are not exported; signature unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No effect: local attributes are not exported; signature unchanged. |

## Status

landed 20261014T013048-L-3418784 2026-10-14 (merge of deliver/U4/Sheaf.AlgebraicGeometry.MayerVietorisImageChainSquares)
