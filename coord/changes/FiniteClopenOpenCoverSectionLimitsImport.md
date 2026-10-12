# FiniteClopenOpenCoverSection Limits import

## Reason

Limits supplies only proof constructions in this module, so the stage-3 import rule
requires a private import. No declaration signature, definition, or target meaning changes.
The one direct importer, FiniteEtaleClosedSubschemeSection, imports this module privately
and compiles against the repaired module; no adaptation is needed. Thus no transitive
importer loses a public export. The table lists all 156 transitive downstream modules
reported by tools/downstream.py; none is edited or requires a claim or adaptation.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Limits
```

## New

```lean
import Mathlib.AlgebraicGeometry.Limits
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not edited | No signature or meaning change; no adaptation needed. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not edited | No signature or meaning change; no adaptation needed. |
| TargetsCheck | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Defs | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Inversion | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.FourierTransform.Properties.Stalk | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Gabber | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not edited | No signature or meaning change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not edited | No signature or meaning change; no adaptation needed. |

## Status

landed 20261012T135325-L-1696276 2026-10-12 (merge of deliver/U3/Sheaf.AlgebraicGeometry.FiniteClopenOpenCoverSection)
