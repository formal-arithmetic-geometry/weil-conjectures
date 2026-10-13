# picard_pullback_base_change_primal proof imports

## Reason

The primal statement uses no dual module. Remove its unused public Dual import, keep the finite-unit theorem as a private proof import, and import scheme Pullbacks publicly because the unchanged statement needs scheme pullback instances. Add FiniteDescent privately for its proved pullback finite-local-freeness instance. No declaration signature or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
```

## Users

All 161 modules reported by downstream.py are listed. import_prune_check.py passed; no module loses a declaration it textually uses. Direct importers also carry their own Dual or finite-unit imports where needed. No target meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardPullbackBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| TargetsCheck | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Statements unchanged; no adaptation required by static pruning check. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Statements unchanged; no adaptation required by static pruning check. |

## Status

landed 20261013T002356-L-2376358 2026-10-13 (merge of deliver/B2/Sheaf.AlgebraicGeometry.PicardPullbackBaseChangePrimal)
