# CategoryTheory.tower_limit_exact_of_coordinate_maps

## Reason

The source requires commuting maps of inverse systems, omitted from the original Lean
signature. The original claim is false: over Z let F be the zero tower, G the tower with
Z at each level and zero strict transitions, and H the constant Z tower. Take alpha=0
and beta=id. Then lim F=lim G=0 and lim H=Z, so U=V=0 satisfy hU and hV,
all coordinates are short exact and F transitions are surjective, but V is not surjective.
The compatibility hypotheses restore the meaning of Stacks 03CA / 02N1.
Read https://stacks.math.columbia.edu/tag/03CA and /tag/02N1, and the correction-of-lifts
argument at https://stacks.math.columbia.edu/tag/0598.

## Old

```lean
theorem tower_limit_exact_of_coordinate_maps (R : Type u) [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R) (H : ℕᵒᵖ ⥤ ModuleCat.{t} R) (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n)) (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n)) (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧ Function.Surjective (β n)) (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)) (hU : ∀ (n : ℕ) (x : ↑(limit F)), limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) (hV : ∀ (n : ℕ) (x : ↑(limit G)), limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) : Function.Injective U ∧ Function.Exact U V ∧ ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) → Function.Surjective V)
```

## New

```lean
theorem tower_limit_exact_of_coordinate_maps (R : Type u) [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R) (H : ℕᵒᵖ ⥤ ModuleCat.{t} R) (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n)) (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n)) (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))), G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) = α n (F.map (homOfLE (Nat.le_add_right n 1)).op x)) (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))), H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) = β n (G.map (homOfLE (Nat.le_add_right n 1)).op x)) (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧ Function.Surjective (β n)) (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)) (hU : ∀ (n : ℕ) (x : ↑(limit F)), limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) (hV : ∀ (n : ℕ) (x : ↑(limit G)), limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) : Function.Injective U ∧ Function.Exact U V ∧ ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) → Function.Surjective V)
```

## Users

The textual declaration-use search has exactly one external user, Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels.
It is unclaimed in this checkout. All transitive downstream modules are listed below;
none changes its meaning because the sole caller's statement already assumes compatibility.
No definition or target signature changes, so no target definition review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.AdicTowerFiniteLimit | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Algebra.Category.ModuleCat.AdicTowerFreeKernelCorrection | T3 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels | unclaimed | Pass existing hα hβ at line 117; statement and visibility unchanged. |
| Sheaf.Algebra.Homology.MittagLefflerLimitHomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData | B2 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreCandidate | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineKernelImageComparison | S3 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineLimitModel | R1 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineProjections | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleKernel | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedFormalCover | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelAffineBound | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelComponentAffineAnnihilation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelConstruction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelQuotient | V2 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilized | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelStabilizedBound | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitAnnihilators | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitFull | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitQuotient | G1 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineLimit | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineEpi | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineMono | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernelFactorization | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels | T1 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionLimits | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionInternalHom | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionInternalHomAffineCompletionEvaluation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionInternalHomAffineSectionsLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionInternalHomAffineTensorDictionary | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionInternalHomSectionsLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalCompletionExact | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalCompletionMapInjectiveProper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalCompletionMapSurjectiveProper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalCompletionPushforwardLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | E3 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.FlatModuleCompletion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.LimitFlatModules | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlat | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlatOverBase | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.StrictHenselizationCompletionNoetherian | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.StrictHenselizationNoetherian | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| Sheaf.RingTheory.StrictHenselizationRegular | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| TargetsCheck | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No direct use; caller signature unchanged, so no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No direct use; caller signature unchanged, so no semantic change. |

The forced adaptation changes only line 117 from
`R F G H α β hshort U V hU hV` to `R F G H α β hα hβ hshort U V hU hV`.
The original compiles on the shared baseline; against the corrected dependency it fails:
`Application type mismatch: The argument hshort ... is expected to have type`
`∀ n x, G.map ... (α (n + 1) x) = α n (F.map ... x)`.
The adapted module compiles together with the corrected dependency.

## Status

landed 20261013T054223-L-444705 2026-10-13 (merge of deliver/K2/Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps)
