# AlgebraicGeometry.kFlatTensorModelPullbackDescentQLax

## Reason

Repair the returned compile timeout by sharing the tensor structures used by Q,
then exposing the quotient's actual identity unit and tensorator data in
`kFlatTensorModelQuotientLax`. The previous body synthesized a lax structure by
projecting `CoreMonoidal.toMonoidal`; the new body retains its coherence proofs
and writes `ε := 𝟙 _` and `μ := fun _ _ ↦ 𝟙 _` directly. These are definitionally
the upstream quotient structure's data. `tensorModel_isIso` now identifies the
mapped quotient tensorator explicitly with `Qh.map (𝟙 _)`.

The Q tensorator continues to use the original
`Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)` transport.
The existing scheme tensor instance is selected through `inferInstance`.
No theorem signature, universe, visibility, hypothesis, mathematical object,
or target meaning changes. No global instance or proof hole is added, and
no file or proof is split. The cached definitions are local instances.

## Old

Original library definition:

```lean
noncomputable local instance kFlatTensorModelPullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance
```

Returned delivery quotient definition:

```lean
noncomputable local instance kFlatTensorModelQuotientLax (S : Scheme.{uModel}) :
    Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)) :=
  inferInstance
```

## New

```lean
local instance kFlatTensorModelHasTensor (S : Scheme.{uModel})
    (P N : GradedObject ℤ (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :
    GradedObject.HasTensor P N :=
  inferInstance

-- Share the concrete tensor structures instead of rebuilding them in each use of Q.
noncomputable local instance kFlatTensorModelComplexTensor (S : Scheme.{uModel}) :
    MonoidalCategory
      (CochainComplex (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) ℤ) :=
  inferInstance

noncomputable local instance kFlatTensorModelHomotopyTensor (S : Scheme.{uModel}) :
    MonoidalCategory
      (HomotopyCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)) :=
  inferInstance

noncomputable local instance kFlatTensorModelDerivedTensor (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    MonoidalCategory (schemeDerivedCategory S) :=
  inferInstance

-- The quotient tensorator is the identity; record its data without unfolding
-- CoreMonoidal.toMonoidal each time, retaining the original coherence proofs.
noncomputable local instance kFlatTensorModelQuotientLax (S : Scheme.{uModel}) :
    Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ)) :=
  { (inferInstance : Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ))) with
    ε := 𝟙 _
    μ := fun _ _ ↦ 𝟙 _ }

noncomputable local instance kFlatTensorModelQhLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance

noncomputable local instance kFlatTensorModelQuotientCompQhLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (HomotopyCategory.quotient
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (.up ℤ) ⋙
        DerivedCategory.Qh) :=
  Functor.LaxMonoidal.comp _ _

noncomputable local instance kFlatTensorModelPullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  Functor.LaxMonoidal.ofIso
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))
```

## Users

`tools/downstream.py` lists 548 transitive importers. Textual use checks
find no downstream uses of the changed local quotient definition. The sole
direct importer is `Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent`;
its unchanged source and an original-instance signature application compiled
against fresh artifacts. All other importers see the unchanged public signature
and the same definitionally equal tensor data. No target meaning is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel | E1 | Local data repair; existing signature and tensorator preserved. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | P2 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | J3 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorModelInputNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackMateSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitCounit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat | B4 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomAdjunctionIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedHomDirectImageComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents | C2 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedTensorHomCochains | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectOpenSupportDetection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | S3 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectTransportCompact | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | S1 | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportOfBounded | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedOverlapPerfectExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally identical tensor data; no source adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Definitionally identical tensor data; no source adaptation. |
| TargetsCheck | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally identical tensor data; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally identical tensor data; no source adaptation. |

## Status

landed 20261013T113339-L-3182132 2026-10-13 (merge of deliver/E1/Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel)
