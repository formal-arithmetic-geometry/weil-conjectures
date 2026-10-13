# coherentFormalModules_canonicalCokernel_isCoherent

## Reason

Correct proof-only public imports as required by the stage-3 brief. Remove unused
ObjectProperty.Kernels, Preadditive.FunctorCategory, and the redundant
FunctorCategory.Basic proof import. Repair H9 also removes the unused proof import
Limits.Preserves.Shapes.Kernels. No existing declaration signature or
definition changes. The only direct importer, CoherentFormalModulesCokernelClosure,
already imports both affected public modules publicly itself. Every transitive downstream
path passes through that importer, so downstream availability and target meanings are
preserved. No adaptation is required. The final import set compiles locally.

## Old

```lean
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.AlgebraicGeometry.Modules.Tilde

```

## New

```lean
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

```

## Users

Source-only `tools/downstream.py` lists the following transitive importers. The sole direct
importer was read and its two public imports checked. The target statements keep their
meaning since no data, definitions, or declaration types change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ClosedImmersionFormalComparisonTransport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelAnnihilation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ClosedImmersionFormalKernelComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelClosure | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CoherentMapReductionTorsion | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FormalCompletionExact | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| TargetsCheck | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same statements and definitions; imports preserved through CokernelClosure. |

## Status

landed 20261013T005053-L-2551101 2026-10-13 (merge of deliver/A3/Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical)
