# AlgebraicGeometry.Scheme.Modules.tensorBoundary_graded_realization

## Reason

Stage-3 preflight classifies additions of commands such as local attributes and sections
as an interface change and requests this record. The added commands control elaboration
of the proof and its proved private helper. They prevent expansion of tensor pullback
and derived functors. They are local to this module: no existing public signature,
definition, visibility, exported instance, or public import changes.

The declaration's signature was checked with stage3_delivery.diff_module:
statement_changed is empty. The public declarations are unchanged. The new proof imports
are private. No definition used by Challenge.lean changes, so no target statement review
is reopened by this command-only record.

## Old

The original command fragment, verbatim:

```lean
attribute [local irreducible] RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons
```

The declaration had the same signature and a whole-proof sorry.

## New

The new command fragments (the intervening private proof is omitted):

```lean
attribute [local irreducible] AlgebraicGeometry.Scheme.Modules.tensorPullback
  Functor.rightDerived Functor.rightDerivedToHomotopyCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons tensorGradedSection

section GradedProjectionHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] RingedSpace.moduleCohomology

-- A proved private helper follows.
end GradedProjectionHelpers
```

All additions are local elaboration controls or a proved private helper. The theorem
now combines three geometric obligations and the proved boundary diagram; its signature
and visibility are identical. No consumer needs an adaptation.

## Users

Inventory from tools/downstream.py with --uses tensorBoundary_graded_realization:
165 downstream modules and the item itself. The only source mention outside the item
is Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct. No listed source is changed.
For every user the statement and all definitions it uses keep the same public interface;
private proof imports and local attributes are not exported. Holders are this checkout's
claim snapshot; no other holder's file is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLiftingCriterion | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerObstruction | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization | N4 | Own proof changed; public signature unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryLeibniz | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryProduct | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorPowerBoundary | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| TargetsCheck | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature, definition, or exported-environment change; source unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature, definition, or exported-environment change; source unchanged. |

## Status

landed 20261014T004110-L-2836995 2026-10-14 (merge of deliver/N4/Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization)
