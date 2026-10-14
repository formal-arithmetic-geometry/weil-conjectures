# perfect_hom_open_transport_square import interface

## Reason

Repair X-84d86 also adds the proof-only `import all` of `PerfectHomTransport`
to reuse its original private transport calculations, removing all six copied theorems
and the two copied definitions without changing any shared module.

This coherence identity needs PerfectHomTransport, not the representing cocone or
perfect-complex theory. Replace the overly broad public import by the direct statement
module. The theorem's elaborated signature is identical. All new helper declarations are
private and proved. Local attributes are scoped to TransportCalculations and do not change
importers' reducibility settings. Local variables likewise end with that section. The
public theorem retains the original section's derived-category instance signature.

The preflight's conservative command comparison flags the helper section, variable and
local attributes together with the import removal; this record covers those commands too.
No shared definition or statement changes, so no target statement review is reopened.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
import all Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
```

Private proved helpers and a scoped TransportCalculations section are added. During that
section, perfectHomComposition and derivedPullback are locally irreducible and elaboration
respects transparency. The theorem proof also locally respects transparency; its statement
keeps the original option. The mathematical objects, definitions and theorem signatures
remain identical.

## Users

The current source import graph lists 448 transitive downstream modules.
There are two direct importers, both using this module privately and the theorem only in
proofs. PerfectHomOpenRestrictedMaps independently publicly imports
PerfectHomOpenRestrictedEquivFields, which publicly imports PerfectHomPushPullCocone and
DerivedMayerVietorisCanonicalData. PerfectHomOpenRestrictionTransport independently
publicly imports PerfectHomOpenRestrictionMap, which publicly imports both of those same
modules. Thus all formerly visible names are still available through independent imports,
and both interfaces and all transitive downstream interfaces are unchanged. No adaptation
is required. No module other than the claimed item is changed. Holders below reflect the
local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisColumns | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsEven | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedDataExists | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedMaps | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictionTransport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_three | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Perfect_hom_mayerVietoris_geometric_columns_even_zero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | claimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| TargetsCheck | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | claimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | unchanged through independent imports; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | unchanged through independent imports; no adaptation |

## Status

landed 20261014T025144-L-158979 2026-10-14 (merge of deliver/V1/Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare)
