# exists_adjoin_finite_fraction_spec

## Reason

Prune an unused maximal-spectrum import and make the integral-closure tower-top
import proof-only, as required by the module contract. No declaration signature,
definition or target meaning changes. This record documents an import-interface
cleanup, not a mathematical statement change.

## Old

```lean
module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
```

## New

```lean
module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Spectrum.Prime.Topology
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AdjoinFiniteFractionSpec --uses
exists_adjoin_finite_fraction_spec` lists 164 downstream modules in the reviewed
snapshot. Only `Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` directly
imports the item, through a plain proof import. It already has a public import of
`Mathlib.RingTheory.Spectrum.Maximal.Defs` and a plain import of
`Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`, so it loses no
available declarations or instances. Its own exported imports and all signatures
remain the same, hence every further downstream module keeps the same mathematical
statements and definitions. No forced adaptations are necessary. Claim holders
below are from the local coordination snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineComplementReciprocalCover | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.FindGloballyGenerated | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralDimOneAmple | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductor | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux | unclaimed (local snapshot) | Direct proof importer; independently imports both removed public modules; unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| Sheaf.RingTheory.JacobsonDenominatorFunctionField | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| TargetsCheck | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed (local snapshot) | No statement or definition changes; no adaptation. |

## Status

landed 20261013T022410-L-3211779 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.AdjoinFiniteFractionSpec)
