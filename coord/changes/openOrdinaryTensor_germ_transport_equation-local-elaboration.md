# AlgebraicGeometry.openOrdinaryTensor_germ_transport_equation

## Reason

The static preflight treats changes to command text as a possible interface
change, including local irreducibility attributes. This record documents that
command delta. The existing theorem signature, all definitions, all instances,
and both existing public imports are identical. The attributes are explicitly
`local` within this module's namespace; their elaboration effects end with that
scope. The scoped heartbeat setting applies only to this theorem's elaboration.
No exported reducibility attribute or target definition changes. No user needs
adaptation or target-statement re-review.

The new proof uses typed aliases and keeps canonical tensor comparisons folded.
The profiler showed the final functor-map rewrites and kernel checking are the
expensive stages. The file compiles cleanly within the existing 60-second limit;
the wall-clock limit has not been changed.

## Old

No local irreducibility or per-theorem heartbeat commands preceded the theorem.
Its signature was:

```lean
theorem openOrdinaryTensor_germ_transport_equation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let C₀ := C z
    let C₁ := C z.val
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    let k₀ := HomologicalComplex.homologyMap
      (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
      (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
        (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
    let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
      (comparisonStalkHomologyIso X' z.val
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    ∀ (τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
        (F.mapHomologicalComplex (.up ℤ)).obj T),
      (∀ n : ℤ,
        τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
          F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
            F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
              (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
            γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) →
      F₀.map k₀ ≫ F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
        ((T₀.sc i).mapHomologyIso F₀).inv ≫
          HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
            F.map k
```

## New

The proof has been replaced by the chain-square, homology naturality and
representative-coherence assembly. Before the same signature are these scoped
elaboration commands:

```lean
attribute [local irreducible] tensorStalkIso tensorComplex openPinnedTensorRestrictionIso
attribute [local irreducible] openDerivedAdditiveStalkIso comparisonStalkHomologyIso

set_option maxHeartbeats 1200000 in
-- The homology comparisons involve several composed functors and localization factors.
```

The theorem signature remains exactly:

```lean
theorem openOrdinaryTensor_germ_transport_equation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV'))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (z : (f' ⁻¹ᵁ V').toScheme) (i : ℤ) :
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).Additive :=
      schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
    letI : (schemeOpenRestriction X (f ⁻¹ᵁ V)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_additive _
    let Q₀ := ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapHomologicalComplex (.up ℤ)).obj P
    let C₀ := C z
    let C₁ := C z.val
    let T₀ := tensorComplex (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀
    let T := tensorComplex f f' g g' sq z.val P
    let F₀ := forget₂ (ModuleCat.{u} C₀) AddCommGrpCat.{u}
    let F := forget₂ (ModuleCat.{u} C₁) AddCommGrpCat.{u}
    let H₀ := comparisonStalkCohomology (f' ⁻¹ᵁ V').toScheme z i
    let β := singleComplexOpenTensorRestrictionMap g' (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj P
    let ν := openDerivedAdditiveStalkIso X' (f' ⁻¹ᵁ V') z i
    let k₀ := HomologicalComplex.homologyMap
      (tensorStalkIso (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ z Q₀).hom i ≫
      (comparisonStalkHomologyIso (f' ⁻¹ᵁ V').toScheme z
        (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q₀) i).inv
    let k := HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z.val P).hom i ≫
      (comparisonStalkHomologyIso X' z.val
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv
    let L₀ := RingedSpace.moduleStalkFunctor (f' ⁻¹ᵁ V').toScheme.toRingedSpace z
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (f' ⁻¹ᵁ V'))
        (L₀ ⋙ F₀) ≪≫ Scheme.Modules.restrictStalkNatIso (f' ⁻¹ᵁ V').ι z
    ∀ (τ : (F₀.mapHomologicalComplex (.up ℤ)).obj T₀ ≅
        (F.mapHomologicalComplex (.up ℤ)).obj T),
      (∀ n : ℤ,
        τ.hom.f n ≫ F.map ((tensorStalkIso f f' g g' sq z.val P).hom.f n) =
          F₀.map ((tensorStalkIso (f ∣_ V) (f' ∣_ V')
            (g.resLE V V' hV') j sq₀ z Q₀).hom.f n) ≫
            F₀.map (L₀.map ((openPinnedTensorRestrictionIso g'
              (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj).inv.app (P.X n))) ≫
            γ.hom.app ((Scheme.Modules.tensorPullback g').obj (P.X n))) →
      F₀.map k₀ ≫ F₀.map (H₀.map β) ≫
          ν.hom.app (DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
        ((T₀.sc i).mapHomologyIso F₀).inv ≫
          HomologicalComplex.homologyMap τ.hom i ≫ ((T.sc i).mapHomologyIso F).hom ≫
            F.map k
```

## Users

`tools/downstream.py` with `--uses openOrdinaryTensor_germ_transport_equation`
reports two direct textual users (including the defining module). The table
also lists its entire downstream import-closure inventory; none sees
a changed signature, definition, instance, public import or exported attribute.
No adapted module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermEquation | C3 | Complete replacement proof; signature identical; commands are proof-local. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Q2 | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | T3 | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreBetti | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | P4 | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkEquivalence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenOrdinaryComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexTargetLocality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| TargetsCheck | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No changed signature, definition, instance or exported attribute; no adaptation. |

## Status

landed 20261013T215557-L-895137 2026-10-13 (merge of deliver/C3/Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermEquation)
