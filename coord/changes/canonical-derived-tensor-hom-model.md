# Canonical derived tensor-Hom representative model

## Reason

Extract the representative definitions to let two new proof modules import them without importing their own consumer. This is not a compile-time split: all files fit the single-file limit. Every moved definition keeps its exact signature, body and public visibility. New function-valued normalization imposes the same equations without bijectivity. No target statement or meaning changes.

## Old

```lean
/-- The functorial resolution already used by derived internal Hom, with the scheme's
Grothendieck instance supplied explicitly.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomKInjectiveResolution (X : Scheme.{uCD}) :
    CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ :=
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  CochainComplex.kInjectiveResolutionFunctor.{uCD} _

/-- Inverse of the localized quasi-isomorphism into the fixed resolution.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomResolutionInverse (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj ((schemeHomKInjectiveResolution X).obj M) ⟶
      DerivedCategory.Q.obj M := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _
    ((CochainComplex.toKInjectiveResolution.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))).app M)).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) M).2
  exact inv (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{uCD} _).app M))

/-- The localization factorization for the fixed functorial K-injective model.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeDerivedInternalHomResolutionIso (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M)) := by
  haveI : IsGrothendieckAbelian.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact (Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{uCD} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{uCD} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, M)

/-- The uncurried component of a map into the fixed Hom complex.
Source: Stacks Project, cohomology.tex, Tag 08DJ, componentwise evaluation.
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeTensorHomUncurryComponent (X : Scheme.{uCD})
    (P L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h' : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    P.X p ⊗ L.X q ⟶ ((schemeHomKInjectiveResolution X).obj M).X n :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  (β_ (P.X p) (L.X q)).hom ≫
    (SheafOfModules.tensorHomEquiv (L.X q) (P.X p)
      (((schemeHomKInjectiveResolution X).obj M).X n)).symm
      (φ.f p ≫ (Classical.choose (Classical.choose_spec
        (homComplex_exists (R := X.sheaf)))) L
          ((schemeHomKInjectiveResolution X).obj M) p q n h')

/-- Naturality and the actual representative evaluation equation characterize the family.
The chain map ψ is fixed on every total-tensor summand by currying the degree-p
component of φ, projected to Hom(L^q,I(M)^(q+p)). The symmetry restores the order
P^p tensor L^q. The localization factorization and resolution map fix both targets.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def IsCanonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          schemeTensorHomUncurryComponent X P L M φ p q n h') ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)
```

## New

The same declarations, with the identical text above, now reside in `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel`, publicly imported by their original module. That module adds the normalization predicate `IsCanonicalDerivedTensorHomMap`; no definition selects arbitrary data from an existence theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | U4 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | M2 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | A3 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | E3 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | H3 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | W3 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| TargetsCheck | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Identical definitions re-exported; no adaptation or semantic change. |

## Status

landed 20261013T011931-L-2764584 2026-10-13 (merge of deliver/M4/Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom)
