# AlgebraicGeometry.singleComplexInheritedTensorCondition

## Reason

Correct the intermediate theorem's interface to the actual map in Stacks
perfect.tex, Tag 0DJA(1), and the DAG statement. That map uses canonical tensor
transitivity, rather than an arbitrary strong monoidal structure. The previous
interface quantified over every monoidal instance and provided no way to apply
it to the caller's pinned tau. Proving a separate arbitrary-tensorator
independence theorem is neither supplied by the source nor needed by the caller.
The earlier candidate asserted that unsupported theorem; this delivery removes it.

The correction is authorized by stage-3 brief section 4 and item step 5 for
wrong or unusable intermediate interfaces. It is substantive and requires CODEX
review. It does not establish the old, universally quantified assertion, and
must not be counted as proving that stronger assertion. No counterexample to
that assertion is claimed. The revised theorem binds the actual canonical tau
and its defining predicate, as the existing SingleComplexBaseChangeCriterion
already does. Canonical comparison existence is already in the library, so this
adds no mathematical hypothesis to the source statement. The monoidal existence
clause is retained. Every target statement and every definition stays unchanged.

There is no natural-language statement_change: the existing DAG statement is
already the canonical assertion of the source, and is byte-identical. Its Lean
record and actual proof route change.

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
          ((derivedPullback g').obj E.obj ◁ φ)) 
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
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K.obj K'.obj φ)
    (τ : ∀ E L : schemeDerivedCategory X,
      (derivedPullback g').obj (E ⊗ L) ⟶
        (derivedPullback g').obj E ⊗ (derivedPullback g').obj L)
    (hτ : IsCanonicalPullbackTensorComparison g' τ) :
    Nonempty (Functor.Monoidal (derivedPullback g')) ∧
    ∀ E : schemeDerivedQCohCategory X,
      SingleComplexBaseChange.StalkCondition f f' g g' sq
        (E.obj ⊗ K.obj) (((derivedPullback g').obj E.obj) ⊗ K'.obj)
        (τ E.obj K.obj ≫
          ((derivedPullback g').obj E.obj ◁ φ)) 
```

The existing public imports remain. CanonicalPullbackTensorComparison is added
as a public import because its predicate occurs in the corrected signature.
The proof-only DerivedTensorTransitivity import is replaced by the new coordinate
lemma. No existing module's instance, definition or elaboration attribute changes.

## Users

The read-only downstream.py scan listed 379 transitive importers.
The --uses scan and a whole-library word search found no use of this declaration
outside its defining module. In particular SingleComplexBaseChangeCriterion only
imports the item, still has its own whole-proof hole, and already binds tau,h_tau.
Its target and every other downstream statement are identical; none needs an
adaptation. All listed importers are recorded below with holders from the local
claim snapshot. No module owned by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | Y3 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | H3 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | J1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | F1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion | Q4 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | P4 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | S2 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | T4 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | H1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | H1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | Y3 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| TargetsCheck | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Does not reference the changed theorem; no proof or signature adaptation. |

## Status

landed 20261013T060423-L-584555 2026-10-13 (merge of deliver/N3/Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition)
