# Sheaf.Paper.CechCupPullbackCompat comparison proof import

## Reason

The second reading found that CechComparisonMapNaturality supplies only a theorem
used in the proof of cechRefinement_composition_naturality. All signature-level
comparison definitions remain public through CechCupProduct and ModuleCechComparison.
Demote the proof dependency to a plain import. The three direct importers already
use plain imports of this module, so this dependency was not exported through them.
The two direct importers that use cechComparisonMapNaturality also import its module
explicitly; the scalar external-cup module does not use it. No declaration type,
definition, target meaning, or downstream interface changes. No adaptations.

## Old

```lean
public import Sheaf.Paper.CechComparisonMapNaturality
```

## New

```lean
import Sheaf.Paper.CechComparisonMapNaturality
```

## Users

Read-only tools/downstream.py reports the following transitive users. Claims are
from the repository snapshot; none is edited in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechComparison | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechGenerators | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftComparisonComplexes | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightCechDiagram | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechComparison | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupHomology | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarCechExternalCup | S1 | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged statements and definitions; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged statements and definitions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged statements and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged statements and definitions; no adaptation. |

## Status

landed 20261013T161727-L-1459870 2026-10-13 (merge of deliver/D4/Sheaf.Paper.CechCupPullbackCompat)
