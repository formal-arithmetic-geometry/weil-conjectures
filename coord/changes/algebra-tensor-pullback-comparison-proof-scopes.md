# AlgebraicGeometry.Scheme.Modules.exists_algebraTensorPullbackComparison

## Reason

Repair cfdb205fd: the private scalar-action helper now binds `{U X}`, `f`, `B` and
`G` explicitly and expands all occurrences of the arbitrary algebra and its structure
map in its signature. The affine module's identically printed private helper instead
fixes these to `f_* O_U` and `f.c`. This is the explicit-binder remedy requested by the
return; the elaborated type and proof of our helper are unchanged. No affine-module
adaptation or import is required.

Preflight classifies added `open`, `open scoped`, section variables and local notation
commands as a visibility change, requiring this record. They support proved private helpers
and the constructed algebra pushout comparison. No existing definition, statement, universe,
binder or visibility changes. No public import is added or removed. All extra imports are
proof-only. No target meaning changes and no downstream adaptation is necessary.

## Old

```lean
open CategoryTheory AlgebraicGeometry
```

The public theorem signature is unchanged:

```lean
theorem exists_algebraTensorPullbackComparison {X Z : Scheme.{u}} (j : Z ⟶ X)
    (a : tensorPullback j ⊣ pushforward j) (B : X.CommAlgebraSheaf) :
    ∃ (C : X.CommAlgebraSheaf) (p : B ⟶ C)
      (e : (pushforward j).obj ((tensorPullback j).obj
        (commAlgebraSheafModule X.sheaf B)) ≅ commAlgebraSheafModule X.sheaf C),
      (commAlgebraSheafModuleFunctor X.sheaf).map p =
        a.unit.app (commAlgebraSheafModule X.sheaf B) ≫ e.hom
```

## New

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped ChangeOfRings
```

Two closed sections contain local shorthand notation for ring forgetting, scalar
restriction and inverse image; the first section binds the scheme morphism and algebra
for `inverseRestrict_smul` and `inverseRestrictIso`. All new helper declarations are private
and proved. The canonical helper has a local heartbeat budget of 800000 because elaborating
the dependent inverse-image scalar actions exceeds the default budget; the single file
compiles within the prescribed 60 seconds. The public theorem retains exactly the Old
signature and all pre-existing public imports. The notation and section variables do not
export a new declaration or affect importing statements.

## Users

The only direct importer and external textual user of the theorem is
`Sheaf.AlgebraicGeometry.TensorGradedAlgebraData`. The table lists every transitive downstream
module returned by `tools/downstream.py`; none needs a Lean edit. Holder information is from
the local claim records at the time of this report. No other held module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedActionProjection | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedQuotientMultiply | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapLocalMultiplication | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionOnSummand | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecond | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecondDiagonal | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedAlgebraData | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedDegreeData | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedKernelLocalIdeal | Q3 | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedKernelSquareZero | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorGradedQuotientActionHomogeneous | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorHomogeneousKernelAction | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorIdealSectionLocalMultiplication | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TensorKernelSectionProduct | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.tensorGradedAction_projection_first | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.AlgebraicGeometry.tensorGradedAction_projection_second | unclaimed | Signature and visibility unchanged; no adaptation required |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Signature and visibility unchanged; no adaptation required |
| TargetsCheck | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Defs | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Properties | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Signature and visibility unchanged; no adaptation required |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Signature and visibility unchanged; no adaptation required |

## Status

landed 20261014T071234-L-3199546 2026-10-14 (merge of deliver/S1/Sheaf.AlgebraicGeometry.AlgebraTensorPullbackComparison)
