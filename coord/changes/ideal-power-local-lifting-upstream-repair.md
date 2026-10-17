# ideal_power_evaluation_eventually_zero and ideal_power_quotient_local_lifting_section

## Reason

The e47efb5a5 upstream sync commented out both declarations and cleared their Lean
attachments. The retained item proof therefore could not resolve either name.
The sync notes record `Unknown identifier ideal_power_evaluation_affine_eventually_zero`
and `Unknown identifier ideal_power_local_maps_eventually_agree`, respectively.
Both supporting modules are unclaimed. Restore their original signatures and complete
proofs against the current upstream APIs, without adapting modules held by another group.

The second reading found that `ideal_power_local_maps_eventually_agree` has now
been restored by M4, with only the permitted axioms. Section lifting reuses that
public theorem directly. Global evaluation vanishing applies it to the global
map restricted to the top open and the zero map on that same open; naturality
supplies the evaluation hypothesis, and componentwise extensionality returns the
global zero equation. All copied private affine and overlap proofs are removed.
No definition or theorem statement is altered, and all proof imports are private.

## Old

At the current base these declarations are commented out. Their verbatim signatures
are retained in the respective nodes' `lean_before_upsync_e47` records:

```lean
theorem ideal_power_evaluation_eventually_zero
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
    ∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), r n m h ≫ φ = 0

theorem ideal_power_quotient_local_lifting_section
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
    (hq : ∀ (n m : ℕ) (h : n ≤ m),
      cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) :
    ∀ s : Γ(F, U), ∃ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      (cokernel.π (a n)).app U s = φ.app U (one n)
```

## New

The two signatures in `## Old` are restored verbatim, with complete Lean proofs.
All public imports remain identical. Only proof bodies and proof imports change. The two existing node attachments are restored from `lean_before_upsync_e47`;
proof routes now describe reuse of local eventual agreement and finite affine gluing.

## Users

`tools/downstream.py` was run for both supporting modules with `--names` and with
`--direct --uses`. The following includes both restored modules and every consumer
returned by that source scan. The final section module no longer imports the
evaluation module; the item imports both supporting modules privately.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero | unclaimed | Restore original signature; reuse proved local agreement; simplify proof imports. |
| Sheaf.AlgebraicGeometry.IdealPowerQuotientLiftingSection | unclaimed | Restore original signature; reuse proved local agreement; simplify proof imports. |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentHomsOverOpen | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIdealPatchingExactSequence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbedding | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingCore | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIdealPatchingGenericEmbeddingStalkBijective | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationGenericStep | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealConstruction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralGenericIdealMap | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIntegralIdealsOfSmallSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleConstructibleReflection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleGenericReflection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleLocallyConstantStrata | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeModuleFiniteOpenAssertionsTransfer | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldExtensionDerivedDirectImageExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleInfinitesimalSystem | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleThickeningLift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteNoetherianSchemeSplitting | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFinitePushforward | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.IdealPowerQuotientLocalLifting | H1 | Use restored declarations; preserve original statement. |
| Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedEtaleLifting | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.DepthThreePuncturedFiniteFlatModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.DvrPuncturedCoverPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteEtaleModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularCodimensionTwoFiniteFlatStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisPuncturedRootChart | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitCharts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitDivisorCharts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitFlat | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionMaximalIdeal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionResidueSeparable | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionUnramified | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitEtaleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericNormalizationCharts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericPuncturedRootChart | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.TraitGenericRootModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.NumericalPolynomialLeadingTerm | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteGeometricPoint | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionsOverQuasiCompactOpen | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.ConstantFiniteSubmoduleVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageLargeFilteredColimit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothBaseChange.TorsionConstantPrimeDevissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveAlgClosedExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothLimitDerivedDirectImageExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitReductionSpectrumComponents | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SplitTensorAlgebraSchemeComponents | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningAffineScheme | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ThickeningIntegral | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | A4 | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteConstantCokernel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | B2 | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | B3 | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | M1 | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEtaleRealizationFull | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleLisseFiniteModels | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleOriginFromFiniteModels | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Paper.ProjectiveCurveBettiCardinalities | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization | E3 | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Targets.EtaleSmooth | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.Targets.EtaleSmoothRing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| TargetsCheck | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineCount | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.AffineGeneric | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.BaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.ExtensionInvariance | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericRestriction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.CurvePairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerElement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairingMonodromy | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorCoefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionCount | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorLifting | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorMonodromyHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | B3 | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.FieldExtensionInjective | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.SupportDimension | XR6cb7e6eacb2063cd | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ConstructibleSheaf.OfForget | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ConstructibleSheaf.RestrictScalars | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Composition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Devissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.FiniteLowerStarLift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BidualitySupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDual | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DoubleDualProper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBiduality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheafShiftedHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Counterexample | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AlgClosedField | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FlatModel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.WeilComplex | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.Statement | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive importer; no statement or definition changes; no adaptation. |

No consumer statement changes meaning. Both restored modules and the item compile
together against the published library; no other consumer needs adaptation.

## Status

landed 20261017T013735-L-114074 2026-10-17 (merge of deliver/H1/Sheaf.AlgebraicGeometry.IdealPowerQuotientLocalLifting)
