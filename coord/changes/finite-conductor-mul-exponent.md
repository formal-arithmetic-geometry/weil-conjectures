# Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow

## Reason

STATEMENT-DISPUTED: the original universally quantified exponent is not necessarily a
conductor exponent. At r = 0, z = 1, the assertion forces A to equal the image of B.
For example let B = Q[t^2,t^3] localized at (t^2,t^3), K = Q(t), and A = B[t].
B is a Noetherian local domain of dimension one; t is integral over B, so A is finite.
Its fraction field is K, but t does not lie in B. The original conclusion for a = t
is therefore false. This is an imported-statement error, not a source error.

Stacks 09N2, https://stacks.math.columbia.edu/tag/09N2, gives a suitable exponent.
Add its base-ring conductor property as an explicit hypothesis; the only caller already
obtains exactly that property, then discards it. The corrected ideal-map assertion is
proved without any sorry, using Ideal.map_pow and Submodule.span_induction.
This correction is not counted as proving the original false assertion.

## Old

```lean
theorem Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K]
    {r : ℕ} (z : A)
    (hz : z ∈ (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))) ^ r)
    (a : A) : ∃ c : B, algebraMap B K c = (z : K) * (a : K)
```

## New

```lean
theorem Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K]
    {r : ℕ}
    (hconductor : ∀ b : B, b ∈ (Ideal.jacobson (⊥ : Ideal B)) ^ r →
      ∀ a : A, ∃ c : B, algebraMap B K c = algebraMap B K b * (a : K))
    (z : A)
    (hz : z ∈ (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))) ^ r)
    (a : A) : ∃ c : B, algebraMap B K c = (z : K) * (a : K)
```

## Users

The downstream command lists transitive importers. Text search finds only one actual
use of the changed declaration, in SemilocalDimOneConductorPower. Its theorem signature
and visibility stay identical. Its two forced proof edits are:

- `obtain ⟨r, hr, _⟩` becomes `obtain ⟨r, hr, hconductor⟩`.
- `hdim A (a ^ r) hpow` becomes `hdim A hconductor (a ^ r) hpow`.

The first retains the necessary argument; the second supplies it at the only call.
No target declaration or definition changes. The caller still proves the same
conductor-power conclusion by the same unit route. All transitive importers listed
by tools/downstream.py are inventoried below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AffineComplementReciprocalCover | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FindGloballyGenerated | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.IntegralDimOneAmple | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductor | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower | unclaimed | Forced proof adaptation: retain hconductor and pass it to the corrected helper. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| Sheaf.RingTheory.JacobsonDenominatorFunctionField | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| TargetsCheck | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration usage; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration usage; existing statements and proofs unchanged. |

## Status

landed 20261013T003201-L-2430156 2026-10-13 (merge of deliver/U3/Sheaf.AlgebraicGeometry.FiniteConductorMul)
