# homComplex_mappingCone_differential import narrowing

## Reason

The proof and statement use only the HomotopyCofiber API. The broader
HomotopyCategory.MappingCone module is unnecessary. The Abel tactic is
needed only for a private proof, so its import is plain, not public.
No theorem signature, definition, or target meaning changes.

## Old

```lean
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
```

## New

```lean
public import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Tactic.Abel
```

## Users

`tools/downstream.py Sheaf.Algebra.Homology.HomComplexMappingConeDifferential
--uses homComplex_mappingCone_differential` lists these modules. Its sole direct
importer, HomComplexMappingCone, independently publicly imports the old
MappingCone module (line 11), preserving availability for every downstream
module. No adaptations are necessary and no statement meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Algebra.Homology.DerivedHomFiniteFreeModelAux | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Algebra.Homology.HomComplexMappingCone | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineKoszulScalarExtComparison | N1 | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.CoherentExtVanishing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | P3 | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulExtOffRankStalk | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulExtRankSupport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheafNonnegative | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SheafExtCoherent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SheafExtStalkLocalization | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Paper.DerivedInternalHomStalkLocalization | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| TargetsCheck | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged: sole direct importer HomComplexMappingCone publicly imports MappingCone itself. |

## Status

landed 20261013T100214-L-2501182 2026-10-13 (merge of deliver/W3/Sheaf.Algebra.Homology.HomComplexMappingConeDifferential)
