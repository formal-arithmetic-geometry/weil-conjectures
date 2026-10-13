# AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_ranks

## Reason

Prune the redundant direct public Flat import. `FlatPullbackStalk` is still publicly
imported and itself publicly imports `Mathlib.AlgebraicGeometry.Morphisms.Flat`, so the
exported declaration closure of the original module is preserved. Existing signatures,
definitions and visibility are unchanged. The new geometric lemmas are imported privately
for the proof. No target changes meaning and no statement review is reopened.

## Old

The original public-import block, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
```

## New

The public-import block after removing the redundant edge, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.PicardBaseChangeStalkRanks --uses
picardRankMatch_baseChange_stalk_ranks` lists 165 downstream modules. The sole downstream
textual user of this theorem is `Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange`,
which imports `Flat` directly too. Its statement is unchanged. For every other downstream
module, the public import graph still reaches exactly the same Flat module via the retained
public `FlatPullbackStalk` edge. Therefore no downstream statement or definition changes,
and no adaptation is needed. The table records all 165 modules from that script as requested;
claim holders are the current locally available claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | W4 | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| TargetsCheck | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No change to exported Flat declarations, statements, definitions or proofs; no adaptation. |

## Status

landed 20261013T005859-L-2608019 2026-10-13 (merge of deliver/V2/Sheaf.AlgebraicGeometry.PicardBaseChangeStalkRanks)
