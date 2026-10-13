# AlgebraicGeometry.koszulCechScalarDivision and koszulCechLocalizedDegreeMap

## Reason

Move the two already constructed definitions into the new evaluation module so the
horizontal lemma can refer to them without importing the original theorem and creating
an import cycle. The original module publicly imports the evaluation module. The original
three public imports remain public through the evaluation module. This is an acyclic
relocation with identical declarations and definitions, not a change to the objects or
statements. The vertical coefficient lemma is proved in the evaluation module. No existing
module other than the item is adapted, and no target meaning changes.

## Old

In Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential:

```lean
noncomputable def koszulCechScalarDivision (e : ℕ) :
    ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) ≃ₗ[A]
      ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) := by
  let N := (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S
  have hu : IsUnit (algebraMap A (Module.End A (↑N)) s) :=
    Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := S) s le_rfl
  exact (LinearEquiv.ofBijective (algebraMap A (Module.End A (↑N)) (s ^ e))
    ((Module.End.isUnit_iff _).mp (by simpa only [map_pow] using hu.pow e))).symm

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Signed restriction of evaluation followed by division by the principal product.
Source: Stacks, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The parameter B supplies the vectors to evaluate on, independently of total degree.
Linearity follows from linearity of cochains, restrictions and scalar division. -/
noncomputable def koszulCechLocalizedDegreeMap (e : ℕ) (n : ℤ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ))) :
    ModuleCat.of A (CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n) ⟶
        principalCechTerms r f F n :=
  ModuleCat.ofHom
    { toFun := fun z J ↦
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ))) (∏ j ∈ J.val, f j) (e + 1)
            ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
              (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
              ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ)) (by ring)) (B J)))
      map_add' := by
        intro z z'
        funext J
        simp only [CochainComplex.HomComplex.Cochain.add_v, ModuleCat.hom_add,
          LinearMap.add_apply,
          map_add, smul_add, Pi.add_apply]
      map_smul' := by
        intro a z
        funext J
        simp only [CochainComplex.HomComplex.Cochain.smul_v, ModuleCat.hom_smul,
          LinearMap.smul_apply,
          map_smul, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
```

## New

In Sheaf.AlgebraicGeometry.KoszulCechLocalizedEvaluation, the same definitions verbatim:

```lean
noncomputable def koszulCechScalarDivision (e : ℕ) :
    ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) ≃ₗ[A]
      ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) := by
  let N := (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S
  have hu : IsUnit (algebraMap A (Module.End A (↑N)) s) :=
    Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := S) s le_rfl
  exact (LinearEquiv.ofBijective (algebraMap A (Module.End A (↑N)) (s ^ e))
    ((Module.End.isUnit_iff _).mp (by simpa only [map_pow] using hu.pow e))).symm

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Signed restriction of evaluation followed by division by the principal product.
Source: Stacks, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The parameter B supplies the vectors to evaluate on, independently of total degree.
Linearity follows from linearity of cochains, restrictions and scalar division. -/
noncomputable def koszulCechLocalizedDegreeMap (e : ℕ) (n : ℤ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ))) :
    ModuleCat.of A (CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n) ⟶
        principalCechTerms r f F n :=
  ModuleCat.ofHom
    { toFun := fun z J ↦
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ))) (∏ j ∈ J.val, f j) (e + 1)
            ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
              (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
              ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ)) (by ring)) (B J)))
      map_add' := by
        intro z z'
        funext J
        simp only [CochainComplex.HomComplex.Cochain.add_v, ModuleCat.hom_add,
          LinearMap.add_apply,
          map_add, smul_add, Pi.add_apply]
      map_smul' := by
        intro a z
        funext J
        simp only [CochainComplex.HomComplex.Cochain.smul_v, ModuleCat.hom_smul,
          LinearMap.smul_apply,
          map_smul, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
```

The original module now has:

```lean
public import Sheaf.AlgebraicGeometry.KoszulCechLocalizedEvaluation
import Sheaf.AlgebraicGeometry.KoszulCechLocalizedBoundary
```

## Users

The source-only downstream script lists the following import closure. Its `--uses`
search finds direct uses only in KoszulCechComparisonConstruction and the item (degree
map), and the item (scalar division). Every transitive importer still receives the same
public declarations. None requires adaptation. Holder names are the local claim snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential | G3 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | S1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineKoszulSectionColimit | S3 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | P2 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineSectionsCompositionComparisons | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulCechComparisonIsIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulCechStageKernel | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulCechStageLifting | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulChainRestrictionFormula | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomChainClassNaturality | J1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomChainEvaluation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomChainRepresentatives | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomComparisonSquare | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomHomologyComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomIdentityEvaluation | V4 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionEventuallyZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenHomRestrictionSurjective | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.KoszulSupportedAugmentationVanishing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate | V4 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedGlobalExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomAdjunctionIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | J3 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedHomDirectImageComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | V4 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | M3 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectOpenSupportDetection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | U4 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | F2 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | S3 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | S1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointMateAffineOpenIsIso | K1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization | K1 | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportOfBounded | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedKoszulRelativeDetector | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedOverlapPerfectExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffine | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| TargetsCheck | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Identical names, signatures, bodies, visibility and inherited public imports. |

## Status

landed 20261013T113342-L-3183419 2026-10-13 (merge of deliver/G3/Sheaf.AlgebraicGeometry.KoszulCechLocalizedDifferential)
