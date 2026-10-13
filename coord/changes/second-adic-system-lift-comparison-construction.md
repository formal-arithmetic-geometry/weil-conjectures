# AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_compatibility

## Reason

Repair of reviewer X-96860 (head 968609027), E2 / review point 4. The old theorem
claimed the square for an arbitrary supplied δ, and is false already on Spec ℚ
with I = K = 0, α = 0 and δ = identity. Tag 088A constructs δ by lifting α.
The reviewer explicitly authorizes the interface below and the exact caller proof.
The repair proves it by supported completion Hom bijectivity, component lifting,
transition faithfulness and natural-transformation assembly. It assumes no square.

The signature needs the ideal-comap interface, so
`Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` is now a public import.
The unused proof import `Mathlib.CategoryTheory.Functor.Currying` is removed.
All new imports are private proof imports. No definition or target statement changes.
No target's meaning changes: the sole direct caller keeps its exact existing signature.

## Old

```lean
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K} (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n)
```

## New

```lean
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K}
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (δ : N ⟶ (completion X K).obj H), ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n)
```

## Users

`tools/downstream.py --uses grothendieckDevissage_secondAdicSystem_lift_compatibility`
finds only the assigned module and its construction caller as textual users. The
following also lists every transitive importer. The construction caller is unclaimed;
only its five proof lines at the end are adapted, as explicitly requested by review.
All of its declarations, signatures, visibility, imports and docstrings are unchanged.
The original caller fails against the corrected dependency at line 90:
`Application type mismatch: The argument H has type CoherentModules X but is expected
 to have type ∀ (e : ℕ), 1 ≤ e → ∀ (hZ : IsNoetherian (K ^ e).subscheme), ...IsEquivalence`.
The repaired caller compiles in the same sandbox overlay.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLift | unclaimed | Forced proof adaptation: supply hthick and obtain delta; all signatures and visibility unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftCompatibility | U3 | Assigned corrected existential construction; private lifting proof added. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | E3 | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| TargetsCheck | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive import user; no declaration reference or adaptation. Statements and definitions unchanged. |

## Status

landed 20261013T060427-L-585743 2026-10-13 (merge of deliver/U3/Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftCompatibility)
