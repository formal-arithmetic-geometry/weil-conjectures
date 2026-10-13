# DiagonalConormalAffineSectionsChosen imports

## Reason

Remove unused AffineConormalSections and BaseChangeConventions imports, and the redundant
DiagonalConormal import (already public through DiagonalConormalDerivation). Keep the added
sectionwise uniqueness import proof-only. No declaration signature or definition changes.
The only direct importer, DiagonalConormalAffineSectionsBase, imports this module proof-only
and explicitly imports the three removed modules itself. Its public signatures depend on
DiagonalConormalDerivation, retained publicly here and there. All indirect users therefore
retain their public dependencies. No target meaning changes or forced adaptations.

## Old

```lean
module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
public import Sheaf.AlgebraicGeometry.AffineConormalSections
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.DiagonalConormal
```

## New

```lean
module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
import Sheaf.AlgebraicGeometry.DiagonalConormalAffineSectionsUnique
```

## Users

Read-only downstream source scan, with current local claim holders. The direct importer
is checked by compiling its original source against the changed module in a scratch sandbox.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | claimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | claimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.DiagonalConormalAffineComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.DiagonalConormalAffineSections | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.DiagonalConormalAffineSectionsBase | unclaimed | Direct proof-only importer; already imports the removed modules itself. |
| Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | claimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalIdealConormalRank | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.Paper.GaloisLisseRepresentations | claimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No change: removed imports were not exported by the direct importer. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No change: removed imports were not exported by the direct importer. |
| TargetsCheck | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | claimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No change: removed imports were not exported by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No change: removed imports were not exported by the direct importer. |

## Status

landed 20261013T011932-L-2764859 2026-10-13 (merge of deliver/N1/Sheaf.AlgebraicGeometry.DiagonalConormalAffineSectionsChosen)
