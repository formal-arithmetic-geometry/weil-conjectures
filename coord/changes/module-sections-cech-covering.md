# AlgebraicGeometry.Scheme.module_sections_surjective_of_cech_h1_vanishing

## Reason

The Lean statement omitted the requirement that members of Cov cover U. Taking
Cov I V hV := IsEmpty I satisfies both original hypotheses, using empty refinements
and zero degree-one cochains, as the original module's checked private witnesses show.
It would therefore assert that every epimorphism of module sheaves is surjective on
all sections. For example, on P¹ over a field, the exact sequence
0 → O(-2) → O(-1) → k(p) → 0 at a rational point has section map 0 → k.

Stacks 01EU explicitly assumes a cofinal system of **open coverings**. Add hcover
so that the Lean interface expresses this unchanged DAG statement. Also use index
universe max u v: the neighborhood cover indexed by the points of U is available
in this universe, whereas arbitrary Type v need not contain it. No target statement
or definition is changed. Existing callers already use index universe max u w.

## Old

```lean
theorem module_sections_surjective_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : Opens X)
    (Cov : ∀ (I : Type v) (V : I → Opens X), (∀ i, V i ≤ U) → Prop)
    (hcofinal : ∀ (I : Type v) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (∀ x, x ∈ U → ∃ i, x ∈ V i) →
      ∃ (K : Type v) (W : K → Opens X) (hW : ∀ k, W k ≤ U),
        Cov K W hW ∧ ∀ k, ∃ (i : I), W k ≤ V i)
    (hcech : ∀ (I : Type v) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (hCov : Cov I V hV) →
      ∀ (f : ∀ i, V i ⟶ U),
      ∀ (Scech : SiteCechComplex V f),
        IsZero ((Scech.cohomologyFunctor 1).obj
          ((S.X₁.val.presheaf)))) :
    Function.Surjective (S.g.val.app (op U))
```

## New

```lean
theorem module_sections_surjective_of_cech_h1_vanishing
    (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : Opens X)
    (Cov : ∀ (I : Type (max u v)) (V : I → Opens X), (∀ i, V i ≤ U) → Prop)
    (hcover : ∀ (I : Type (max u v)) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      Cov I V hV → ∀ x, x ∈ U → ∃ i, x ∈ V i)
    (hcofinal : ∀ (I : Type (max u v)) (V : I → Opens X) (_hV : ∀ i, V i ≤ U),
      (∀ x, x ∈ U → ∃ i, x ∈ V i) →
      ∃ (K : Type (max u v)) (W : K → Opens X) (hW : ∀ k, W k ≤ U),
        Cov K W hW ∧ ∀ k, ∃ (i : I), W k ≤ V i)
    (hcech : ∀ (I : Type (max u v)) (V : I → Opens X) (hV : ∀ i, V i ≤ U),
      (hCov : Cov I V hV) →
      ∀ (f : ∀ i, V i ⟶ U),
      ∀ (Scech : SiteCechComplex V f),
        IsZero ((Scech.cohomologyFunctor 1).obj
          ((S.X₁.val.presheaf)))) :
    Function.Surjective (S.g.val.app (op U))
```

## Users

The downstream.py listing contains 628 modules. Only
Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion actually calls the declaration.
Its original proof fails against the corrected interface at line 96 with:
`Invalid ⟨...⟩ notation: The expected type ∀ x ∈ U, ∃ i, x ∈ V i is not an inductive type`.
The new hcover obligation shifts the old cofinality proof into the covering slot.
The adaptation inserts exactly these three lines after the Cov argument:

```lean
    · intro I V hV hcover x hx
      rw [← hcover] at hx
      exact TopologicalSpace.Opens.mem_iSup.mp hx
```

These prove the necessary covering obligation from the existing iSup equality.
Every original declaration signature and visibility is identical. The adapted caller
compiles; no other line in that module changes. ModuleCechVanishingBasis merely
imports this module and has no call to adapt. All other downstream modules use
unchanged interfaces, and no definition used by Challenge is changed. The global
build remains the maintainer's check.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | Z2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedCounitHomologyFactorization | M2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization | R2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineDerivedCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineDerivedConcentration | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison | Z2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange | W3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineSinglePushforwardUnitIso | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | N2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmpleIdealSection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmplePullbackIdealAffineSection | T2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeMapCech | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | A2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.BoundedCoherentFiniteTorDirectImagePerfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CechResolution | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper | C2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentArtinRees | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModule | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentHomsOverOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentProjRepresentation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentSerreVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CoherentSupportUnionExactSequence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CompletionInternalHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ComponentSupportedAffineSection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | T2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | P2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageCohomologyCoproduct | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageCoproductAffineTruncation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageTruncatedCoproduct | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageUniformAffineTruncation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedGlobalSectionsCohomologyCoproduct | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DerivedTensorUnitCompact | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | Q2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.EtaleOfInfinitesimalRestrictionsProper | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.EtaleOpenOfInfinitesimalRestrictions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteAffinePushforwardIdealDevissage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | N3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardCoherent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteSchemeCohomologyTensor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | T2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalCompletionExact | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalFibreCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalKernelGradedPieces | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalModuleSupportConstant | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalSystemsKernelReesFinite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalSystemsPullback | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | R3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GlobalSectionsSeparable | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | H2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HilbertDifference | Z2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.InfinitesimalTransitionThickening | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IntersectionNumber | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.LerayDegenerateSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.LerayEdgeVanishingIso | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.LerayLowDegree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.LeraySpectralSequence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.LocallyFreeExtNaturality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis | unclaimed | Imports the module but does not call its theorem; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion | unclaimed | Forced adaptation: add the covering witness at the existing call; all signatures unchanged. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMap | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase | M2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Modules.VeryAmpleDisjointUnion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedImmersionOfSurjectiveStructureStalks | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NoetherianPerfectDirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.OpenRestrictionSupportTriangle | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallGluing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectComplexClassesSmallGluingCore | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | S3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | Q2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectObjectCompact | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Picard.FlatInvertibleCanonicalDerivedBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDualityPairingNaturality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperDirectImageFiniteTor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | E1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperPerfectDirectImagePerfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.PushforwardRankOnOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QcOpenDerivedLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal | Q3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativeSerreVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativeSpecBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SerreCriterionAffineness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SerreSectionCoordinateSurjective | R3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleComponentFinite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleFinite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SerreSectionModuleTailFinite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | Z2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | Z2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SplitReductionSpectrumComponents | R1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | B2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TheoremFormalFunctions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ThickeningAffineHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | V2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TruncatedDirectImageAffineFiniteSupport | V1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.TwistedSectionFiniteCoordinates | V2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.UniformDirectImageBoundCore | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ValuationClosedFibreSectionVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ValuationLimitQcohSectionDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.VanishingProjective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.AlgebraicGeometry.ZeroSupportFiniteScheme | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.BaseChangeClosureComponents | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.CechCupPullbackCompat | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.CechRefinementCochainMap | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.EulerCharacteristicWellDefined | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.FiniteStructureAlgebraLift | U3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.FiniteStructureProperSupport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.FiniteSurjectiveCoherentGenericSupport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.GradedFinitenessCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.HigherDirectImagePresheaf | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.MLCohomologyPowersIdeal | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparisonSections | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| TargetsCheck | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex | M2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocus | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections | J1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Projective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Serre | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | B3 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | F1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Modules.AffineHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Modules.Ample | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.Degree | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.RationalPoint | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.Representability | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Gabber | M1 | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature, definition, or target meaning changes; no call of the corrected theorem. |

## Status

landed 20261012T160145-L-2567368 2026-10-12 (merge of deliver/X2/Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1)
