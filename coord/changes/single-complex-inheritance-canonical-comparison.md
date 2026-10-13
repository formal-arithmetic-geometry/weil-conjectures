# AlgebraicGeometry.singleComplexInheritedTensorCondition

## Reason

Correct the intermediate Lean statement to the induced canonical tensor comparison in
Stacks Tag 0DJA(1), pinned by IsCanonicalPullbackTensorComparison and the shared
K-flat/counit equation. Its old quantification over every unrelated monoidal structure
is stronger than the source and does not specify that map. No counterexample to that
stronger assertion is claimed. This is a source/interface correction under stage 3
section 3, not a proof of the retired stronger assertion.

The prior bridge was refused because its proposed tensorator comparison lacked an
isomorphism on the localized base-derived source commuting with the comparison.
The corrected bridge uses the canonical equation instead. All E, all degrees, all
points, unbounded complexes, and every coordinate system remain included. No
Challenge target, or definition used by a Challenge target, changes.

## Old

```lean
theorem singleComplexInheritedTensorCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ) :
    Nonempty (Functor.Monoidal (derivedPullback g')) ∧
    ∀ [Functor.Monoidal (derivedPullback g')] (E : schemeDerivedQCohCategory X),
      SingleComplexBaseChange.StalkCondition f f' g g' sq
        (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
        ((Functor.Monoidal.μIso (derivedPullback g') E.obj K.obj).inv ≫
          ((derivedPullback g').obj E.obj ◁ φ)) := by sorry
```

## New

```lean
theorem singleComplexInheritedTensorCondition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    (K : schemeDerivedQCohCategory X) (K' : schemeDerivedQCohCategory X')
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ) :
    ∃ m : (derivedPullback g').CoreMonoidal,
      IsCanonicalPullbackTensorComparison g' (fun A B ↦ (m.μIso A B).inv) ∧
      ∀ E : schemeDerivedQCohCategory X,
        SingleComplexBaseChange.StalkCondition f f' g g' sq
          (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
          ((m.μIso E.obj K.obj).inv ≫ ((derivedPullback g').obj E.obj ◁ φ))
```

The delivered module contains the complete proof from the two intermediate obligations.

## Users

Both declaration callers are currently unclaimed. The criterion already has a
canonical comparison and its predicate; uniqueness identifies it with the returned
model. The Tor-independent proof uses the returned canonical core-monoidal model.
Their theorem signatures and visibility remain byte-identical. All other downstream
modules listed below contain no use of the changed declaration. Their mathematical
statements and the definitions they use are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality` | G1 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.CartesianTensorDataComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DivisorClassCurve` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.DivisorPicRepresentative` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenericComponentsSplit` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibres` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GenusInvariant` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HenselianClopenRestriction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardMorphism` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.HilbertToPicardSurjective` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange` | A3 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardCupProductBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality` | M3 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardDirectImageTestSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` | H1 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` | H1 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1IntersectionSection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardH1MultipleLocus` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosed` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardProductOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardProductOpenData` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso` | U4 | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericClopen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion` | unclaimed | Forced proof adaptation; existing signatures and visibility unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.SteinFactorizationAffine` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange` | unclaimed | Forced proof adaptation; existing signatures and visibility unchanged. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.AlgebraicGeometry.ValuationProperCoherentSections` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.Paper.GaloisLisseRepresentations` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `Sheaf.Paper.ZariskiH0ProperHenselianPair` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `TargetsCheck` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.Picard` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.SerreDuality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.HenselianConnectedness` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.Slicing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Picard.Scheme` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.AlgebraicGeometry.TheoremOfCube` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No call of the changed declaration; no signature or definition change. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No call of the changed declaration; no signature or definition change. |

## Status

landed 20261013T151700-L-923921 2026-10-13 (merge of deliver/F4/Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition)

## Forced adaptations

Both callers are unclaimed. SingleComplexBaseChangeCriterion replaces the old
conjunction projection with the returned core model and canonical predicate.
Canonical uniqueness identifies the inverse tensorator with its existing tau.
TorIndependentPerfectTensorBaseChange replaces the old Nonempty/conjunction
destructuring with the returned core model, installing its toMonoidal with an
explicit type annotation. Its original private helpers stay unchanged.
Every existing signature and visibility in both callers is preserved.
The delivery dry run records exact original-against-overlay diagnostics in its
forced-adaptation report; the original conjunction-based applications cannot
elaborate against the changed existential conclusion.
