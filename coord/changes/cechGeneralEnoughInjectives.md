# CategoryTheory.Sheaf.exists_cechDoubleComplex_general

## Reason

Reviewer X-a400d, head a400d7bfa, E2 requires the new derived-section model
assumptions and universes to be replaced exactly unless a genuine proof of the
original arbitrary-large-site model is supplied. The repair uses HasExt in
universe v, EnoughInjectives, covering indices in Type v and coefficients in
AddCommGrpCat.{v}. The restricted statement is exactly the existing
Sheaf.exists_cechDoubleComplex. Repair X-b0ad5 therefore replaces the duplicate
proof with a canonical Lean alias, importing its module. The unnecessary new
model, column and augmented-row comparison modules and nodes are withdrawn.
It is not one of the five Challenge declarations.

## Old

```lean
theorem Sheaf.exists_cechDoubleComplex_general
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C)
    {ι : Type w} {U : ι → C} (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      (∀ q : ℕ, Nonempty
        (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D ≅
        (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
          ((Over.forget X).op ⋙ F.cohomologyPresheaf q))) ∧
      ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X)
```

## New

```lean
alias Sheaf.exists_cechDoubleComplex_general := Sheaf.exists_cechDoubleComplex
```

The alias inherits every binder and universe of the existing theorem. Its
elaborated type is exactly the restricted signature authorized in the previous
repair: HasExt.{v}, EnoughInjectives, indices in Type v, and coefficients in
AddCommGrpCat.{v}. It does not assert the former independent-universe statement.
The four existing public imports stay unchanged. The existing theorem's module
is imported only for this alias proof; its statement uses the public imports.

## Users

The source-only downstream scan found 170 transitive importers. Textual uses
of exists_cechDoubleComplex_general occur only in its own module and the
spectral-sequence caller below. All caller signatures and definitions stay
unchanged; only the invalid general proof is withdrawn. Thus no Challenge
statement or definition used by it changes meaning. Its general proof remains
open and is not claimed established by the restricted helper.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts | Z2 | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CechH1Injective | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | H2 | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.Paper.BoundaryDerivationSquareZero | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| TargetsCheck | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech | unclaimed | Forced proof withdrawal in general spectral-sequence theorem; every signature and visibility unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration uses this helper; statement and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration uses this helper; statement and definitions unchanged. |

The forced adaptation changes the general spectral-sequence proof at original
lines 84--89 to `:= by sorry`. The first declaration's docstring additionally
records the source, full proof plan, and unresolved large-site realization step,
as required for every named sorry. The ordinary import of CechGeneral is also removed: the withdrawn proof no
longer uses it, and the alias now imports this caller module, so retaining the
reverse import would create a cycle. All other imports and proofs stay unchanged. The original compiled against the modified dependencies fails at
84:28 to synthesize HasExt in universe v (typeclass heartbeat limit), and at
84:67 with Application type mismatch: hπ has Sieve.ofArrows.{v,u,w} but the
helper expects Sieve.ofArrows.{v,u,v}. The adapted module compiles. Restoring
that general proof would need additional theory, not a coerced application or
an extra target hypothesis. The caller is currently unclaimed.

## Status

landed 20261013T003202-L-2430493 2026-10-13 (merge of deliver/V2/Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneral)
