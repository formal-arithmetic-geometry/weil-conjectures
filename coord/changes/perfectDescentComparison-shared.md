# AlgebraicGeometry.perfectDescentComparison

## Reason

Share the already counit-pinned canonical comparison with the Hom-transport auxiliaries without duplicating the definition. The new canonical construction is exactly the old expression. The existing name becomes an abbrev of it; the abbreviation is definitionally equal to its old value, and neither the isomorphism nor its choices change. The existing theorem signature is verbatim unchanged. A public import of PerfectHomTransport is necessary for the abbreviation body. No statement or target meaning changes, so no target statement review is reopened.

## Old

```lean
noncomputable def perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  eqToIso (congrArg (fun k ↦ derivedPullback k) (baseChangeMap_fst s g).symm) ≪≫
    (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))
        (baseChangeMap s g) (pullback.fst s T.hom)).symm
```

## New

```lean
noncomputable abbrev perfectDescentComparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  perfectHomComparison s g
```

## Users

The downstream.py --uses scan finds no user outside the item that mentions this name. The table also lists every transitive importer returned by downstream.py. Each keeps exactly the same comparison after expansion; none requires a forced adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | G1 | Canonical comparison becomes a definitionally equal alias; own proof adapted. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | M2 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | J1 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | W3 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| TargetsCheck | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No textual use of the comparison; no type or meaning change and no adaptation. |

## Status

landed 20261013T022414-L-3213338 2026-10-13 (merge of deliver/G1/Sheaf.AlgebraicGeometry.PerfectDescendMorphisms)
