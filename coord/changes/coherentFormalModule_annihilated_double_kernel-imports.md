# coherentFormalModule_annihilated_double_kernel

## Reason

Remove the unused public import Mathlib.Data.List.TFAE from the kernel component module.
It was inherited from the parent equivalence theorem, but this component has no TFAE in its
statement or proof. All remaining original public imports retain their visibility. Proof-only
imports are pruned or routed through the two new helper modules. No signature or definition
changes, so this record documents only the observable import removal.

## Old

The existing theorem signature remains byte-for-byte unchanged. Old import block:
```lean
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
```

## New

The existing theorem signature remains byte-for-byte unchanged. New import block:
```lean
import Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import Sheaf.AlgebraicGeometry.CoherentFormalModuleKernelComponentAffineAnnihilation
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
```

## Users

Read-only downstream.py reports 215 transitive importers. Only
Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated directly imports this module and
mentions its theorem. That module imports this module privately, explicitly publicly imports
Mathlib.Data.List.TFAE itself, and has the same theorem application because the theorem type
is unchanged. Consequently neither it nor any of its transitive importers loses TFAE or
changes statement meaning. The unchanged direct importer compiled successfully through
lcompile.py against the delivered modules. No adaptations are necessary; no file held by another group is
changed. Holder snapshots below are from this machine's coord/claims records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | U4 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.CoherentMapReductionTorsion | M1 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_kernel | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | P2 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| TargetsCheck | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement or definition changes; direct importer explicitly imports TFAE. |

## Status

landed 20261013T003157-L-2428654 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleKernel)
