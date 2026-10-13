# CategoryTheory.Over.DescentDatum.glued_model_chart_pullbacks

## Reason

Repair the existing false intermediate criterion. For nonempty X take p and j to be
identities, V=X coproduct X, U its first component, q its component isomorphism and
q₀ the fold map. The original hypotheses hold but U -> V is not an isomorphism,
so its chart square cannot be cartesian. The necessary missing condition is that
the inverse image of each target chart is its specified source open.

This is the overlap equality implicit in Stacks Project, Tag 0AP4:
https://stacks.math.columbia.edu/tag/0AP4 . The sole Lean caller now proves it from
actual descended overlaps, without any new hypotheses or holes. No target statement
or public definition changes. The unit record has no realized step at this node;
the unit's effective-descent route is preserved.

## Old

```lean
theorem glued_model_chart_pullbacks
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀) :
    ∀ i, IsPullback (q i) (U i).ι (j i) q₀
```

## New

```lean
theorem glued_model_chart_pullbacks
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : ∀ i, q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    ∀ i, IsPullback (q i) (U i).ι (j i) q₀
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback --uses glued_model_chart_pullbacks`
finds only the item itself and Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts as
declaration users. The table records every transitive importer as well. The caller
is unclaimed in this checkout. Its original proof obtains arbitrary weak glued data,
which supplies no inverse-image equality, so it cannot satisfy the repaired criterion.
It must retain the descended overlap construction instead.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts | unclaimed | Forced proof adaptation; signature and visibility unchanged; reconstruct actual gluing to prove inverse-image equalities. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| TargetsCheck | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer only; all public statements and definitions it uses are unchanged. |

The forced caller edits are proof imports (lines 11–13), a proved private helper
(lines 31–66), and the existing theorem body (from line 107). The private helper
uses the overlap cartesian squares to prove inverse-image equality. The theorem
body constructs precisely the same descended-overlap gluing as before, retains its
data, glues q₀ and proves the new required condition before invoking the repaired
criterion. Repeating this construction is necessary because the old auxiliary
existentials forget the overlap identifications. Only proof code, proof imports
and this private helper change; the existing caller signature and docstring are
identical to the baseline. No unrelated declaration or file is adapted.

The unchanged original caller, compiled against the corrected item, fails at line 77:

```text
error: Type mismatch
  glued_model_chart_pullbacks U W q W₀ q₀ j hcart hopen hcover₀ hover hcomm
has type
  (∀ i, q₀ ⁻¹ᵁ (j i).opensRange = U i) →
    ∀ i, IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  ∀ i, IsPullback (q i) (U i).ι (j i) q₀
```

The adapted caller compiled without warnings. The unchanged original also compiles
against the shared baseline, as verified by deliver3.py's counterfactual checks.

## Status

landed 20261013T211058-L-390145 2026-10-13 (merge of deliver/E3/Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback)

## Landing repair X-275d6

Retain the caller's original plain import of
`Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`. The landing import-prune check
reported that `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` loses access
to `AlgebraicGeometry.Scheme.baseChangeMap` when this import is removed.
Keeping it is the reviewer's requested repair and avoids any downstream
adaptation. Neither theorem proofs nor signatures change in this repair.
The other two removed caller proof imports remain unnecessary on the new route.
