# pullbackTensorModelMap

## Reason

The original complete module repeatedly exceeded its 60-second check, including
its unchanged baseline. Reuse the existing named instances from
DerivedPullbackMonoidalDescent instead of rebuilding their values inline.
The total complex and canonical predicate use the same named base tensor and
preadditivity instances. The localization map explicitly uses pullbackDescentQLax.
Proved private generic lemmas share the categorical proof terms within this module.
No module or proof is split to evade the limit and no checker is disabled.

All three changed definitions are definitionally equal to the originals.
The scratch audit DefinitionEqualityAudit.lean checks each equality by
with_unfolding_all rfl against the compiled original module. Thus all existing
statements retain exactly their meaning, including the targets depending on
these definitions. Their semantic review can confirm this by the three rfl
checks; no binder, universe, visibility or target statement is changed.
No adapted module is necessary because conversion is unchanged.

## Old

```lean
def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  CochainComplex.mapBifunctor P N (curriedTensor _)

def pullbackTensorModelMap (X : Scheme.{uTC})
    [HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ⟶
      DerivedCategory.Q.obj (pullbackTensorTotal X P N) := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{uTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : CategoryTheory.Limits.HasColimitsOfSize.{0,0}
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0,0,uTC,uTC} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))
  haveI (A B : GradedObject ℤ (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  letI := HomologicalComplex.monoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) (.up ℤ)
  haveI : (DerivedCategory.Q
      (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))).LaxMonoidal := inferInstance
  exact Functor.LaxMonoidal.μ (DerivedCategory.Q
    (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) P N

def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.monoidalCategory T.sheaf
  letI := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlat → N.IsKFlat →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{uTC} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          ((SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)
```

## New

```lean
def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := pullbackDescentModuleTensor X
  CochainComplex.mapBifunctor P N (curriedTensor _)

def pullbackTensorModelMap (X : Scheme.{uTC})
    [HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ⟶
      DerivedCategory.Q.obj (pullbackTensorTotal X P N) := by
  letI := pullbackDescentModuleTensor X
  letI := moduleSymmetric X
  haveI := modulePreadditive X
  letI := moduleClosed X
  haveI := moduleGrothendieck X
  haveI := moduleResolutions X
  haveI := moduleDerivedMonoidal X
  exact @Functor.LaxMonoidal.μ _ _ _ _ _ _ _ (pullbackDescentQLax X) P N

def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := modulePreadditive X
  letI := modulePreadditive T
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlat → N.IsKFlat →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{uTC} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          ((SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)
```

## Users

The table lists every transitive dependent reported by tools/downstream.py,
plus the item. Textual direct uses are recorded in the worker's scratch audit;
the same definitional-equality argument applies to every row.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | K3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison | U2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization | S3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | P2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential | J2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation | S2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | J3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackMateSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | J1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | E1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.MixedGlobalExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents | C2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.NormalizedTensorHomCochains | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectHomGap | C2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | V3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | S2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | G4 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | P2 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | T4 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperPerfectTransportCompact | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | S1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv | J1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | H4 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | H4 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | C1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | N1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap | P3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | K3 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | T1 | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally unchanged; no adaptation |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Definitionally unchanged; no adaptation |
| TargetsCheck | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally unchanged; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally unchanged; no adaptation |

## Status

landed 20261013T100146-L-2492692 2026-10-13 (merge of deliver/U2/Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison)
