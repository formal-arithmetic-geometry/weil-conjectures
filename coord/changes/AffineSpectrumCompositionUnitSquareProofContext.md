# AffineSpectrumCompositionUnitSquare proof context

## Reason

The second reader replaces the false undelivered core with a proved private coherence calculation. The static checker flags the new universe/variable commands, elaboration options and local reducibility attributes as interface commands, so this record documents their scope. Every existing public signature remains byte-for-byte identical; no import, public definition, instance, notation, or target meaning changes. Generic variables occur only in the private-helper namespace. The original Scheme variables are unchanged. Local attributes and options control elaboration in this module and are not exported to importers. The new private definition tc explicitly constructs a composite isomorphism; it chooses no data from an unproved existence theorem.

The old and new proof contexts are shown verbatim below; the unchanged public import and public section are omitted. All downstream modules returned by tools/downstream.py are listed conservatively. None needs adaptation.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w z
open CategoryTheory
-- Prove the coherence calculation with abstract functors, so its algebra does not
-- unfold the constructions of derived categories or derived pullback.
namespace AffineSpectrumCoherence
variable {S : Type u} [Category.{v} S]
  {D : S → Type w} [∀ X, Category.{z} (D X)]
  (F : ∀ {X Y : S}, (X ⟶ Y) → (D Y ⥤ D X))
  (c : ∀ {X Y Z : S} (f : X ⟶ Y) (g : Y ⟶ Z), F g ⋙ F f ≅ F (f ≫ g))
  (i : ∀ X : S, F (𝟙 X) ≅ 𝟭 (D X))
```

The private-helper namespace ends before this concrete proof context:

```lean
namespace AlgebraicGeometry

attribute [local irreducible] derivedPullback
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local implicit_reducible] Scheme.isoSpec asIso
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumBaseChangeComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonCancellation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenAffine | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | none | No interface or target-meaning change; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | none | No interface or target-meaning change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | none | No interface or target-meaning change; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | none | No interface or target-meaning change; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | none | No interface or target-meaning change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | none | No interface or target-meaning change; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | none | No interface or target-meaning change; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | none | No interface or target-meaning change; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none | No interface or target-meaning change; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | No interface or target-meaning change; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | none | No interface or target-meaning change; no adaptation. |
| TargetsCheck | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Defs | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Properties | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | No interface or target-meaning change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | No interface or target-meaning change; no adaptation. |

## Status

landed 20261013T215557-L-894959 2026-10-13 (merge of deliver/C3/Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare)
