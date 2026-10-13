# coherentFormalModules_restriction_preservesKernel imports

## Reason

Second reading removed the redundant direct public import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`. This does not remove any
public declaration: the unchanged public import of
`Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects` already reaches it
through `CoherentFormalModule`, `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`,
`Mathlib.CategoryTheory.Abelian.Transfer`, and `Mathlib.CategoryTheory.Abelian.Basic`.
`PreservesLimit` also remains public through `Preadditive.AdditiveFunctor`,
`Limits.Preserves.Finite`, and `Limits.Preserves.Basic`.
No definition or existing declaration signature changes. No user requires adaptation,
and no target meaning changes. The same proof compiles without this direct import.
Two redundant proof-only imports added by the first worker (kernel construction and
factorization) were also removed: `import all CoherentFormalModuleKernel` exposes them.

## Old

```lean
public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
```

## New

```lean
public import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
```

## Users

All transitive importers reported by `tools/downstream.py` are listed below.
The public import path above is unchanged for each of them; their statements and
available declarations are therefore unchanged. Holder information is the repository
snapshot at second reading; no module in this table is adapted or delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData | B2 | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreCandidate | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedFormalCover | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleLimitAnnihilators | U2 | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImage | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineEpi | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineMono | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionLimits | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FormalCompletionExact | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | E3 | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: the same public Kernels module remains reachable. |
| TargetsCheck | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: the same public Kernels module remains reachable. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: the same public Kernels module remains reachable. |

## Status

landed 20261013T045603-L-137393 2026-10-13 (merge of deliver/T1/Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels)
