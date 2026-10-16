# AlgebraicGeometry.completion_thickening_cokernel_reflection

Also restores `AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel`.

## Reason

Both declarations were disabled by comments during upstream sync e47efb5a5. The assigned torsion theorem needs the cokernel estimate, which needs fixed-thickening reflection. Both dependency modules are unclaimed. Restore their recorded signatures and proofs. Replace access to private helpers of the retired formal-module file with the public exact calculus and a kernel proof of coherence; reuse the existing proved epimorphism helper from the reduction module. The cokernel proof uses ObjectProperty.homMk and the implicit first morphism of cokernel.mapIso. No definition or target statement changes.

## Old

The following recorded signatures occur inside TAKEN OUT block comments, and therefore declare no constants:

```lean
theorem grothendieckDevissage_secondAdicSystem_torsion_cokernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (cokernel (δ.hom.app (op e))))
```

```lean
theorem completion_thickening_cokernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcomplete : ∀ hZ : IsNoetherian (K ^ q).subscheme,
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (cokernel a.hom))
```

## New

The same signatures are restored as public theorems, with complete proofs:

```lean
theorem grothendieckDevissage_secondAdicSystem_torsion_cokernel
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (cokernel (δ.hom.app (op e))))
```

```lean
theorem completion_thickening_cokernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcomplete : ∀ hZ : IsNoetherian (K ^ q).subscheme,
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2
      G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (hred : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (cokernel a.hom))
```

## Users

Full downstream inventory from tools/downstream.py. The only direct importers are the cokernel module and the assigned torsion module, both included here. The original commented declarations have no active textual users. Every existing signature and definition below is preserved. Restoring proof declarations adds no instances or global elaboration attributes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CompletionThickeningCokernelReflection | unclaimed | Restored theorem and repaired proof; no existing signature changed. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion | K2 | Assigned theorem proved; signature unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedEtaleLifting | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedFiniteFlatModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteEtaleModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteFlatStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitEtaleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteGeometricPoint | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel | unclaimed | Restored theorem and repaired proof; no existing signature changed. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | B2 | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteConstantCokernel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | B2 | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteEtaleRealizationFull | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureMultiplicationLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureProductCompatibility | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureProductCore | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureProductExists | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureTensorTestsFaithful | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureUnitLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteStructureUnitLiftExistence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleLisseFiniteModels | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleOriginFromFiniteModels | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Paper.ProjectiveCurveBettiCardinalities | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | A3 | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Targets.EtaleSmooth | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.Targets.EtaleSmoothRing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| TargetsCheck | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineCount | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineGeneric | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.BaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericRestriction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.CurvePairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerElement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairingMonodromy | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorCoefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionCount | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorLifting | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorMonodromyHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.FieldExtensionInjective | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.SupportDimension | XR6cb7e6eacb2063cd | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ConstructibleSheaf.OfForget | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ConstructibleSheaf.RestrictScalars | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Composition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.FiniteLowerStarLift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.BidualitySupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDual | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBiduality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafShiftedHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AlgClosedField | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FlatModel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilComplex | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.Statement | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Main | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing statement and definitions unchanged; no adaptation needed. |

## Status

landed 20261016T221615-L-1616737 2026-10-16 (merge of deliver/K2/Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion)
