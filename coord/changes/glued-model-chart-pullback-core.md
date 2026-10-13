# glued_model_chart_pullback_core

## Reason

The original core and single-chart assertions are false. For nonempty X, let V be two
copies of X, q₀ the fold map, j the identity and U the first component. The local square
is cartesian and the target charts cover, but U is not the inverse image of j.
The sandbox counterexample compiles using only the three permitted axioms.
This repairs only the local open-subscheme criterion. It is not a proof of the old claim.
The false caller keeps its signature and is explicitly left disputed with sorry, rather
than concealing the missing inverse-image equality in a new false intermediate theorem.

## Old

```lean
theorem glued_model_chart_pullback_core
-- STATEMENT-DISPUTED: the stated hypotheses do not force the chart square to
-- be cartesian; a chart may be empty while other charts cover the glued model.
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left) (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : IsOpenImmersion (j i))
    (hover : j i ≫ W₀.hom = (W i).hom)
    (hcomm : q i ≫ j i = (U i).ι ≫ q₀) :
    Nonempty (IsLimit (PullbackCone.mk (q i) (U i).ι hcomm))
```

## New

```lean
theorem glued_model_chart_pullback_core
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left) (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : IsOpenImmersion (j i))
    (hover : j i ≫ W₀.hom = (W i).hom)
    (hcomm : q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    Nonempty (IsLimit (PullbackCone.mk (q i) (U i).ι hcomm))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle | Y3 | Only direct user of core; single theorem signature unchanged, now explicitly disputed and sorry. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.Paper.GaloisLisseRepresentations | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| TargetsCheck | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Defs | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Inversion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Perverse | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Properties | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Gabber | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; not adapted | Uses unchanged single-chart signature transitively; no definition or target statement changes. |

No other module mentions the changed core declaration. The downstream scan found
296 transitive importers; their statements retain the same meaning because only a
proof-level criterion changes. No forced adaptation is delivered.

## Status

landed 20261013T115954-L-3404111 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle)
