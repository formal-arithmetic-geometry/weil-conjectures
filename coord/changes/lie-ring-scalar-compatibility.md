# AlgebraicGeometry.GrpObj.instLieAlgebraLie

## Reason
The preflight's interface checker compares the whole body of an instance, including proof
fields. Filling `lie_smul` therefore requires a change record although this is a proof-only
change. `LieAlgebra` is a Type-valued class extending `Module`, not a Prop-valued
class. Its inherited `Module` field is the same existing `Module.compHom` instance
in both versions; only the proposition-valued `lie_smul` field changes. Thus proof
irrelevance identifies those proof fields, while the module data and the existing
bracket remain identical. No user requires adaptation and no target's mathematical
meaning changes.

## Old
```lean
noncomputable instance : LieAlgebra R (Lie G) where
  lie_smul := by sorry
```

## New
```lean
noncomputable instance : LieAlgebra R (Lie G) where
  lie_smul := by
    intro c x y
    change ⁅x, (Scheme.ΓSpecIso (.of R)).inv.hom c • y⁆ =
      (Scheme.ΓSpecIso (.of R)).inv.hom c • ⁅x, y⁆
    exact LieAlgebra.lie_smul _ _ _
```

## Users
`tools/downstream.py WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring --uses
AlgebraicGeometry.GrpObj.instLieAlgebraLie` lists 133 downstream modules and zero textual
mentions of the generated instance name. Every downstream module is listed below.
No modules are adapted or claimed in addition to the assigned item; the proof-only
change cannot strengthen, weaken, or change their statements by proof irrelevance.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.GenusInvariant | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket | not adapted | unchanged by proof irrelevance |
| Sheaf.AlgebraicGeometry.MixedCommutatorTangent | not adapted | unchanged by proof irrelevance |
| TargetsCheck | not adapted | unchanged by proof irrelevance |
| WeilConjectures | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights | not adapted | unchanged by proof irrelevance |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | unchanged by proof irrelevance |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Defs | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Inversion | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Perverse | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Properties | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | unchanged by proof irrelevance |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | unchanged by proof irrelevance |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | unchanged by proof irrelevance |

## Status
landed 20261012T041341-L-1718443 2026-10-12 (merge of deliver/M2/WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring)
