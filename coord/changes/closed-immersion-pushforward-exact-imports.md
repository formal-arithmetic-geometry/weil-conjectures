# ClosedImmersionPushforwardExact imports

## Reason

The proof uses only the two existing stalk lemmas and Mathlib short-complex primitives.
Remove the unused SheafCohomology.Basic import. The Functors and ShortExact imports
are redundant: they remain public through Abelian -> Skyscraper -> Functors and
Abelian -> Grp.AB -> ShortComplex.Ab -> ShortExact, respectively.
No theorem statement, definition, or target meaning changes.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Topology.AbelianSheafShortExactStalkwise
import Sheaf.Topology.ClosedPushforwardAbelianStalks
```

## New

```lean
public import Mathlib.Topology.Sheaves.Abelian
import Sheaf.Topology.AbelianSheafShortExactStalkwise
import Sheaf.Topology.ClosedPushforwardAbelianStalks
```

## Users

The three direct importers were inspected. ClosedPushforwardBoundaryNaturality and
NumericalPolynomialLeadingTerm import ClosedImmersionPushforwardCohomology, which
itself publicly imports SheafCohomology.Basic. SelfExtTorResolutionCore contains no
reference to the abelian-sheaf H or cohomologyPresheaf constructions removed from
this re-export. All users retain Functors and ShortExact through Abelian. No adaptation
is needed. The following table is the complete source-based downstream list from
`tools/downstream.py Sheaf.Topology.ClosedImmersionPushforwardExact --names`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Q2 | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheafNonnegative | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorDualChart | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionCore | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| Sheaf.Topology.ClosedPushforwardBoundaryNaturality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| TargetsCheck | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Redundant imports removed; meanings and signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Redundant imports removed; meanings and signatures unchanged. |

## Status

landed 20261013T201759-L-3972846 2026-10-13 (merge of deliver/K2/Sheaf.Topology.ClosedImmersionPushforwardExact)
