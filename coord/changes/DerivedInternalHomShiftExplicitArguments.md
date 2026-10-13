# CategoryTheory.derivedInternalHom_shift_comparison

## Reason

The original signature elaboration repeatedly unfolds the ringed-site/sheaf
carrier encodings while inferring arguments of derivedInternalHom and forget₂.
Diagnostics at 10,000 heartbeats fail while elaborating the existential family
binder, before its proof. With implicit arguments, repeated compiles exceeded
60 seconds. Explicitly supplying the already determined category C and universes
u,w reduces the same file to 10.8 seconds. These are annotations only: no binder,
hypothesis, object, conclusion, or universe changes. No definition or target meaning
changes, so no target review is reopened.

The private helper shiftComparisonOfOneVariable proves the generic composition
once. It is fully proved, has no new instance or attribute, and changes nothing
an importer sees. No experimental local options or attributes remain.

## Old

```lean
theorem derivedInternalHom_shift_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    ∃ e : ∀ (P Q : DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (m n : ℤ),
      ((derivedInternalHom J R).obj (op P, Q))⟦n - m⟧ ≅
        (derivedInternalHom J R).obj (op (P⟦m⟧), Q⟦n⟧),
      ∀ (P Q Q' : DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (m n : ℤ) (q : Q ⟶ Q'),
        ((derivedInternalHom J R).map ((𝟙 P).op, q))⟦n - m⟧' ≫
            (e P Q' m n).hom =
          (e P Q m n).hom ≫
            (derivedInternalHom J R).map ((𝟙 (P⟦m⟧)).op, q⟦n⟧')
```

## New

```lean
theorem derivedInternalHom_shift_comparison
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] :
    ∃ e : ∀ (P Q : DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) (m n : ℤ),
      ((derivedInternalHom.{u, w} (C := C) J R).obj (op P, Q))⟦n - m⟧ ≅
        (derivedInternalHom.{u, w} (C := C) J R).obj (op (P⟦m⟧), Q⟦n⟧),
      ∀ (P Q Q' : DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
        (m n : ℤ) (q : Q ⟶ Q'),
        ((derivedInternalHom.{u, w} (C := C) J R).map ((𝟙 P).op, q))⟦n - m⟧' ≫
            (e P Q' m n).hom =
          (e P Q m n).hom ≫
            (derivedInternalHom.{u, w} (C := C) J R).map ((𝟙 (P⟦m⟧)).op, q⟦n⟧')
```

The differences are only explicit universe arguments on CommRingCat, RingCat,
and derivedInternalHom and the explicit implicit parameter `(C := C)` on
derivedInternalHom. The declaration's elaborated type and visibility are identical. A temporary
module with the original unannotated statement was proved by directly applying
the delivered theorem and compiled successfully; that verification module is
not included in the delivery.

## Users

The sole downstream textual user of derivedInternalHom_shift_comparison is
Sheaf.AlgebraicGeometry.GlobalHomShiftedHypercohomology; its existing application
continues to infer exactly the same arguments. The full transitive downstream list
is included conservatively below; annotation changes have no semantic effect in
any module, so no module requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomShiftedHypercohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same elaborated type; no adaptation required. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Same elaborated type; no adaptation required. |
| TargetsCheck | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same elaborated type; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same elaborated type; no adaptation required. |

## Status

landed 20261013T125007-L-3835621 2026-10-13 (merge of deliver/D2/Sheaf.Algebra.Homology.DerivedInternalHomShiftComparison)
