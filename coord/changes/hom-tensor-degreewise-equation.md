# homTensorProjection, homTensorSectionMap, HomTensorCurryCondition

## Reason

The forward and reverse parts must import the curry equation without importing
its existence theorem. Expanding it in their signatures repeatedly unfolds large
monoidal and Hom product constructions and made the upper proof exceed the
60-second file limit. Extracted exactly these constructions into a shared module;
the old names are abbreviations of them. Bodies are definitionally equal to their old
versions; no statement or mathematical notion changes and no hypothesis is added.
The original theorem and all target signatures remain unchanged.

## Old

```lean
noncomputable def homTensorProjection (L M : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) L M).X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (M.X q) :=
  (Classical.choose (Classical.choose_spec (homComplex_exists (R := R)))) L M n p q h
```

```lean
noncomputable def homTensorSectionMap (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    A.val ⊗ B.val ⟶ (A ⊗ B).val := by
  let := SheafOfModules.monoidalCategory R
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val
```

```lean
def HomTensorCurryCondition (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n) → Prop := by
  let := SheafOfModules.monoidalCategory R
  intro a
  exact ∀ (p q : ℤ) (U : Cᵒᵖ)
    (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)),
    let φ := ((homTensorProjection R
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
      n (p + q) (p + q + n) rfl).val.app U).hom ((a.val.app U).hom s)
    let ψ := ((homTensorProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl).val.app U).hom s
    let χ := ((homTensorProjection R L M (p + n) q (p + q + n)
      (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
    (φ.app W).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p q (p + q) rfl).val.app (op W.unop.left)).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y
```

## New

```lean
noncomputable abbrev homTensorProjection (L M : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) L M).X n ⟶ SheafOfModules.homObj (R := R) (L.X p) (M.X q) :=
  homTensorCurryProjection R L M n p q h
```

```lean
noncomputable abbrev homTensorSectionMap (A B : Mod) :
    letI := SheafOfModules.monoidalCategory R
    A.val ⊗ B.val ⟶ (A ⊗ B).val :=
  homTensorCurrySectionMap R A B
```

```lean
abbrev HomTensorCurryCondition (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n) → Prop := by
  exact HomTensorDegreewiseEquation R K L M n
```

The shared module contains the original bodies verbatim except for renaming the
three identifiers. There is one construction of each notion; existing names are
abbreviations with their unchanged declared types and visibility. A target's meanings
do not change: every alias unfolds to the original body, so this extraction does
not reopen semantic review. There is no adaptation of another held module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalizedTensorHomCochainComponents | unclaimed | The component formula uses homTensorProjection at its unchanged type; its body remains definitionally equal. No adaptation. |
| Sheaf.Algebra.Homology.HomTensorDegreewise | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorCurryNaturalPure | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorDifferential | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorDifferentialComponent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorDifferentialSummand | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorLocalizedExt | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorNaturality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorNaturalityComponent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorSectionNaturality | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.HomTensorTotal | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.KInjectiveHomComplex | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Algebra.Homology.RhomGlobalSections | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorDerivedGlobalSections | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactDetection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedHomotopyTensorHom | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparisonDual | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedStabilizedLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectCompactTests | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectPreservesCompact | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectTransportCompact | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RestrictedGlobalHomShiftedEquiv | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationModel | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedAffineOverlapMap | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDetectorOpenLiftCore | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineAttachment | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| TargetsCheck | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Definitionally identical bodies; statements unchanged; no adaptation. |

## Status

landed 20261013T100227-L-2505217 2026-10-13 (merge of deliver/Y3/Sheaf.Algebra.Homology.HomTensorDegreewise)
