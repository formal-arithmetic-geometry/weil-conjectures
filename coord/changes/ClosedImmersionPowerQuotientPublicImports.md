# ClosedImmersionPowerQuotient public imports

## Reason

`TensorPullbackAdjunction` supplies a theorem needed only by proofs. The public signature needs
`tensorPullback`, defined in `TensorPullback`. Export the latter directly. The proof obtains the
adjunction declarations through the proof-only import of `ClosedImmersionUnitQuotient`.
No existing declaration signature, definition, or visibility changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.TensorPullback
```

## New

```lean
public import Sheaf.AlgebraicGeometry.TensorPullback
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ClosedImmersionPowerQuotient` was rerun
by the second reader. There are now two direct importers: `CompletionFromRestriction`
and `ThickeningSystemPushforwardTermwiseLift`. Both import the item privately,
neither references either adjunction-existence declaration, and both compile unchanged
against the delivered module. The narrowed export does not propagate past those
private imports. No module needs adaptation and no target meaning changes.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.CompletionFromRestriction` | unclaimed | Signature and definitions unchanged; compiled unchanged against the delivered module. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement` | H2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence` | J2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GrothendieckExistence` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.SupportedThickeningDictionary` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardLifting` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardTermwiseLift` | unclaimed | Signature and definitions unchanged; compiled unchanged against the delivered module. |
| `Sheaf.AlgebraicGeometry.ThickeningSystemsCompletionComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.ThickeningSystemsEquivalence` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.ConstructibleSheaf.SylowCoverStalkData` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.AlgebraizeFiniteOverProper` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.AlgebraizeFiniteStructureAlgebra` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.FiniteStructureAlgebraLift` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.FiniteStructureAlgebraOperationsLift` | P2 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.GaloisLisseRepresentations` | H1 | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.IntegralCoverTrivialCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `TargetsCheck` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No effect: the direct importers import the item privately; its adjunction export does not propagate. |

## Status

landed 20261013T010617-L-2671894 2026-10-13 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ClosedImmersionPowerQuotient)
