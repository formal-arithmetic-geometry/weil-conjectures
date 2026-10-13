# glued_model_chart_pullback_single

## Reason

The old statement is false; Y3 already checked the two-component counterexample.
For a nonempty scheme X, set Y = W₀ = X, p = identity, V = X coproduct X over X
by the fold map, U the first component, W the identity object, q the component
isomorphism, j = identity, and q₀ the fold map, with a singleton index. The local
cartesian square, target cover, over-map equation, and commutativity all hold.
The asserted square would make the first-component inclusion an isomorphism,
although it misses the second component. The inverse image of range(j) is all
of V, not U. Adding source coverage alone would not fix overlapping target
charts: both components could map to the same identity target chart.

Require the missing inverse-image equality explicitly. The corrected theorem
is proved from the already proved core and IsPullback.of_isLimit. It works for
empty opens and empty schemes without any nonemptiness assumption. For j the
identity, the new hypothesis forces U = top and excludes the counterexample.
This is a statement repair, not a proof of the original false theorem.
No target or definition changes; the conclusion and all old binders remain.
The actual gluing construction must supply the new equality.

## Old

```lean
theorem glued_model_chart_pullback_single
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀) :
    IsPullback (q i) (U i).ι (j i) q₀
```

## New

```lean
theorem glued_model_chart_pullback_single
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    IsPullback (q i) (U i).ι (j i) q₀
```

## Users

Read-only downstream.py --uses found one external direct user, and 296 transitive
importers. Every listed importer is recorded below. Only the direct caller is
adapted; all other existing signatures and target statements retain their meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Q2 | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback | unclaimed | Forced adaptation: signature unchanged; invalid application replaced by disputed sorry. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| TargetsCheck | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive user only; caller signature unchanged, so no adaptation or statement change. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle | N4 | Held statement repaired and proved; core unchanged. |

## Forced adaptation

The unchanged original Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback
compiled against the baseline. After compiling the corrected item into the sandbox
and compiling the unchanged original against it, Lean reported:

```
lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelChartsPullback.lean:28:2: error: Type mismatch
  glued_model_chart_pullback_single U W q W₀ q₀ j i (hcart i) hopen hcover hover hcomm
has type
  q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i → IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  IsPullback (q i) (U i).ι (j i) q₀
```

The direct caller's proof lines 27–28 are replaced by exactly `sorry`. Its signature
and visibility stay byte-for-byte identical. Its docstring is necessarily expanded
to record STATEMENT-DISPUTED, the source, intended missing step, and counterexample:
no complete proof in words exists under the unchanged false hypotheses. The now
unused private proof import is removed under the brief's mandatory pruning rule.
No other lines or declarations are changed. The caller is unclaimed on this checkout.
The adapted module compiles. Its existing node is updated to record the dispute
and its absence of proof dependencies, rather than an invalid application.

## Status

landed 20261013T201805-L-3975293 2026-10-13 (merge of deliver/N4/Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle)
