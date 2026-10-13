# AffineSpectrumCoordinateRepresentatives module-local elaboration settings

## Reason

The delivery tool classifies changes to module commands, including local elaboration settings,
as interface changes and requires this record. Elaborating the tensor-pullback compositions
without local opacity reached the 200000-heartbeat limit before completing the module.
Marking the tensor-pullback definitions and composition comparison locally irreducible,
with explicit types on the chain map, permits the proof to compile within the compiler limit.
The two backward transparency options support the existing `.Modules`/`SheafOfModules`
identifications in this proof. These commands do not change any declaration type or body
outside this module, and every original public signature and public import stays identical.
No target's statement or meaning changes; no definition has been changed.

## Old

The original elaboration-setting command was:

```lean
set_option autoImplicit false
```

The original module had no local irreducibility registrations.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Inside the existing namespace, for this module only:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
```

Every existing public signature is identical. The duplicate private helper has been removed; its computation is reused from
`IsomorphismPullbackCounit.counit_isIso_kFlat`, exported by the new helper module. All extra imports of the original module are proof-only imports.

## Users

The following is the complete transitive downstream inventory from `tools/downstream.py`.
All rows preserve their statements and definitions because the settings and attributes
are scoped to the importing module's proof elaboration; none is adapted. The only direct
use of the original public theorem outside its own module is
`Sheaf.AlgebraicGeometry.AffineSpectrumStalkCondition`; that use keeps exactly the same type.
Holders are those recorded in this clone when the record was generated.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineSpectrumStalkCondition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | M3 | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | H1 | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenAffine | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| TargetsCheck | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: identical public signatures and imports; added opacity attributes are local. |

## Status

landed 20261013T142900-L-499164 2026-10-13 (merge of deliver/P4/Sheaf.AlgebraicGeometry.AffineSpectrumCoordinateRepresentatives)
