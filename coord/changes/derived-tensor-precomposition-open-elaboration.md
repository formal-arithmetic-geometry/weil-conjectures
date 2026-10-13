# AlgebraicGeometry.exists_derivedTensor_precomposition_open

## Reason

Preflight conservatively treats file-level elaboration commands as an interface change.
The proof adds `Limits` to the open namespaces, local exact-composition and additive
instance registrations, and options for elaborating localization comparisons. These commands
are used only while checking this module: no global instance or notation is registered.
The one declaration signature and all public imports are identical. No definition used
by a target is changed, and no target statement needs reopening. The second reader should
verify the scope of these commands. No downstream source is adapted.

## Old

The original file had `open CategoryTheory MonoidalCategory` and no additional proof
elaboration commands. Its theorem signature was:

```lean
theorem exists_derivedTensor_precomposition_open
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i)) :
    ∃ e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
        𝟙_ (schemeDerivedCategory X),
      schemeDerivedQCohProperty X ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj) ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map
          ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
            e.hom ▷ P.obj ≫ (λ_ P.obj).hom))
```

## New

The theorem retains exactly the same signature:

```lean
theorem exists_derivedTensor_precomposition_open
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i)) :
    ∃ e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
        𝟙_ (schemeDerivedCategory X),
      schemeDerivedQCohProperty X ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj) ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map
          ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
            e.hom ▷ P.obj ≫ (λ_ P.obj).hom))
```

The proof additionally uses these elaboration commands:

```lean
open CategoryTheory MonoidalCategory Limits
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The pullback-local-invertibility private theorem also has a scoped `maxHeartbeats` limit
of 1200000, with a comment explaining the extra definitional-equality work. All added
helpers are private and proved, and neither new public data nor a new axiom is introduced.

## Users

`tools/downstream.py` finds 340 transitive downstream modules; only
`Sheaf.AlgebraicGeometry.AdjointTensorAnnihilatorTransport` directly mentions the theorem.
Every module in the textual downstream listing is recorded below. These elaboration
commands do not change any imported declaration, so no original module fails to compile
because of them and no forced adaptation is proposed. Holders are read from the local
claims at preparation time; the second reader may refresh them.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen | K1 | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AdjointTensorAnnihilatorTransport | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same statement and definitions; no adaptation needed. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Same statement and definitions; no adaptation needed. |
| TargetsCheck | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same statement and definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same statement and definitions; no adaptation needed. |

## Status

landed 20261013T130034-L-3923421 2026-10-13 (merge of deliver/K1/Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen)
