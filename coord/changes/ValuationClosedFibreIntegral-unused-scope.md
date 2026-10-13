# AlgebraicGeometry.Scheme.Modules.closed_fibre_is_integral (unused scoped opening)

## Reason
The delivery preflight conservatively treats removal of any open command as a visible command change and requires a change record. The removed scoped opening controls elaboration in this module only. It was unused in the theorem signature and proof; its sole supporting private import is also unused. No declaration signature, definition, instance, public import, or target meaning changes.

## Old
```lean
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
open scoped AlgebraicGeometry.Scheme.Modules
```

## New
Both lines are removed. All declaration signatures, definitions (there are none), and public imports remain identical.

## Users
Ran tools/downstream.py Sheaf.AlgebraicGeometry.ValuationClosedFibreIntegral --uses AlgebraicGeometry.Scheme.Modules.closed_fibre_is_integral: 155 downstream modules, and only ValuationClosedFibreDivisibility directly mentions the theorem. Read that user's source: it already imports Modules.Invertible publicly and opens the scope itself. Its use takes the exact same arguments and conclusion. Every other downstream module sees the identical theorem type and public imports; removing this local open command cannot change its elaboration. No adaptation is required. No target review is reopened because no definition or statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ValuationClosedFibreIntegral | claimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.AlgebraicGeometry.ValuationClosedFibreDivisibility | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| TargetsCheck | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Defs | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Properties | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | None: same theorem type and public imports; removed local scoped opening only. |

## Status
landed 20261013T002007-L-2357682 2026-10-13 (merge of deliver/C4/Sheaf.AlgebraicGeometry.ValuationClosedFibreIntegral)
