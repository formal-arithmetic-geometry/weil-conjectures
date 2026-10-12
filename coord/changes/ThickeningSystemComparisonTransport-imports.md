# ThickeningSystemComparisonTransport-imports

## Reason

The closed-immersion full-faithfulness theorem is used only in the proof, so its
import must be private. The unchanged signature requires tensorPullback, previously
re-exported through that theorem module; expose its defining module directly.
This changes import visibility, not any declaration, definition, or target meaning.
The only direct importer, ThickeningSystemHomTransport, imports this module
privately and already separately imports ClosedImmersionPushforwardFullyFaithful
and TensorPullback. Hence no declaration or instance it needs is lost, and no
transitive public interface crosses this private import boundary. No adaptation.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
```

## Users

Listed by tools/downstream.py; only the direct importer uses the target theorem.
Every existing signature and definition stays identical. No target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.ThickeningSystemHomTransport | unclaimed | No statement change; sole direct importer privately imports this module and independently imports closed-immersion theorem. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No statement change; beyond sole private import boundary. |
| TargetsCheck | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No statement change; beyond sole private import boundary. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No statement change; beyond sole private import boundary. |

## Status

landed 20261012T220520-L-1393566 2026-10-12 (merge of deliver/H1/Sheaf.AlgebraicGeometry.ThickeningSystemComparisonTransport)
