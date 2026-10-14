# AlgebraicGeometry.perfectDescentComparison

## Reason

Repair the class-2 normalization defect in coord/hollow-definitions.md and
coord/repairs.txt. The prior abbreviation re-used a comparison selected from
exists_derivedPullbackComposition. Its specification pins the comparison only
relative to newly selected counits on the already fixed functors, allowing those
counits to be rescaled. Sharing that choice did not repair the normalization.

The new comparison is constructed by leftDerivedLift from the original universal
presentation retained as recordedPullbackData. It uses the original K-flat counits,
the canonical underived tensor comparison, and equality transport along
baseChangeMap_fst. Properties of these constructions are proved from the original
universal and K-flat properties. No new pullback functor is selected and no arbitrary
witness of a mere-existence theorem is introduced. The primary universal
functor/counit presentation remains the one used to define derivedPullback; no fresh
counit is selected from the composition existence theorem for the repaired data.

The old composition family appears only in the proof of the change-of-counit theorem
and the continuity transfer. Universal uniqueness gives the natural automorphisms
relating the two systems. Thus the existing Hom continuity theorem is reused instead
of adding an unproved variant. The inverse and finite-equality arguments are the
existing arguments specialized to the new comparisons.

## Old

```lean
noncomputable abbrev perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  perfectHomComparison s g
```

## New

```lean
noncomputable abbrev perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  eqToIso (congrArg (fun k ↦ derivedPullback k) (baseChangeMap_fst s g).symm) ≪≫
    (recordedDerivedPullbackComposition (baseChangeMap s g) (pullback.fst s T.hom)).symm
```

The signature, visibility and abbreviation status are unchanged. The public body now
uses the explicit expression defining recordedPerfectHomComparison; its composition
is the asIso of the explicit
recordedDerivedPullbackCompositionLift. See the four new modules of the delivery for
the complete data construction and invertibility/coherence proofs, the named
normalization proof obligation, and the continuity transfer from that intermediate. The statements of Challenge.lean are untouched.

## Users

The downstream.py --uses perfectDescentComparison scan finds only the assigned module:
there are no external textual callers to adapt. The full transitive import closure
is listed below. Both direct importers compile unchanged against the repaired
module in the second reading (Core 18.5 s; Diagram 16.9 s). Existing signatures and theorem conclusions in every importer stay the same.
Because literal comparison data changed, semantic review of targets whose definitions
or statements use this comparison should be reopened, despite unchanged target text.
The intended canonical derived-pullback comparison and Tag 09RE conclusion are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | V2 | Comparison data repaired; theorem type and clauses preserved. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | H1 | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | Y3 | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | H1 | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | U4 | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| TargetsCheck | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Imports only; no textual use of the comparison or adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Imports only; no textual use of the comparison or adaptation. |

## Status

landed 20261014T080233-L-3750342 2026-10-14 (merge of deliver/V2/Sheaf.AlgebraicGeometry.PerfectDescendMorphisms)

One new named proof obligation remains: exists_recordedPerfectHom_normalization.
It is used solely in the continuity-transfer proof, never to select construction data.
The explicit comparison, its invertibility, and its coherence are proved independently
of this intermediate. The retained counit is irreducible with proved universal/K-flat API
lemmas to avoid unfolding the selected original presentation in downstream elaboration.

The original public PerfectHomTransport import is retained for importer compatibility.
The new construction uses only the recorded comparison; the legacy public names remain
available to existing importers.

Only DerivedPullbackRecordedComposition is added as a public import: the comparison
body uses its explicit composition construction. RecordedPerfectHomTransport is a
proof-only import. The original exported API is retained.

The existing private helper `AlgebraicGeometry.homMap_eq_iff` is also adapted.
Its hypotheses and left-hand comparison equation are identical; the right-hand
conjugated map changes from `perfectHomMap s g f = φ` to
`recordedPerfectHomMap s g f = φ`. It has no external callers and is used only
by the two lifting branches in this module. This private interface change is
forced by the new comparison construction and does not change the public
descent theorem's signature.

Second-reader caller limitation: writing Core's compiled output in an
import-ordered two-module run times out at 60 seconds both on the unchanged
shared baseline and on the repaired overlay. The baseline check is isolated
from every repaired module. The single-file Core and Diagram checks pass,
but no full rebuilt caller chain is claimed. The existing baseline timeout
needs maintainer attention independently of this change.

The additivity repair uses equality transport from `recordedPullbackData_additive`
inside the counit type and the composition proof. It adds no standalone duplicate
tensor-pullback additivity theorem. Explicit typed local bindings replace the
untyped bindings that failed to elaborate in the previous repair.
