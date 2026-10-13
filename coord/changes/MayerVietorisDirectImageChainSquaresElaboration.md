# AlgebraicGeometry.schemeMV_directImage_chain_squares

## Reason

The ordinary comparison is a composite of transported open-site equivalences.
Unification while assembling four chain squares repeatedly unfolded the direct-image
functor, open adjunction, and nested restriction, exceeding the file budget. Keeping
these definitions locally irreducible lets the proof use their naturality and
adjunction APIs instead. The complete file then compiles within the 60-second limit.
The new comparison definition is also irreducible, with its natural-isomorphism API
and separate unit and restriction identities.

The static interface classifier treats local attribute commands as an interface
change and requires this record. All existing public signatures, definitions and
visibility remain identical. The attributes below are local to AlgebraicGeometry's
namespace in this file and expire at its end. No importer acquires them. The new
scoped elaboration options likewise apply only to the declarations they prefix.
No adaptation is forced and no target's meaning changes.

## Old

No local reducibility attributes. The public theorem signature was:

```lean
theorem schemeMV_directImage_chain_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ (a : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I) ⟶
        schemeOpenModuleImageComplex Y U J)
      (b : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I) ⟶
        schemeOpenModuleImageComplex Y V J)
      (c : F.obj (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I) ⟶
        schemeOpenModuleImageComplex Y (U ⊓ V) J),
      f ≫ schemeOpenModuleImageComplexUnit Y U J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ U) I) ≫ a ∧
      f ≫ schemeOpenModuleImageComplexUnit Y V J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ V) I) ≫ b ∧
      a ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_left) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I) ≫ c ∧
      b ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_right) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I) ≫ c
```

## New

The public theorem signature above is unchanged. The proof has these local commands:

```lean
attribute [local irreducible] schemeOpenModuleAdjunction
  schemeOpenModuleImageRestriction RingedSpace.moduleDirectImage
```

Private generic naturality helpers and the constructed termwise chain map are proved
inside the same module. No existing definition's data or theorem statement changes.

## Users

The complete downstream list from tools/downstream.py was checked for interface
effects. Only DerivedMayerVietorisImageResolutionComparisonFirst mentions this theorem;
its statement and visibility are unchanged, so its original proof still applies.
All other entries are transitive importers. None needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData | T4 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisDirectImageBoundary | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonFirst | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.MayerVietorisDirectImageChainSquares | V2 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | R3 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityUnion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | B4 | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMVConePresentation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMVSESPresentation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| TargetsCheck | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Not affected: same public statements and definitions; local attributes expire. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Not affected: same public statements and definitions; local attributes expire. |

## Status

landed 20261013T234524-L-2168379 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.MayerVietorisDirectImageChainSquares)
