# AlgebraicGeometry.PullbackStalkTensor.tensorToStalk

## Reason

The old definition selected ring-map data using Classical.choose from the unproved
exists_tensorToStalk. The human ruling of 2026-10-12 classifies this as hollow data.
Replace it by the actual tensor-product lift of the projection stalk maps.

## Old

```lean
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  Classical.choose (exists_tensorToStalk f g z)
```

## New

```lean
noncomputable def tensorToStalk (z : ↥(Limits.pullback f g)) :
    A f g z ⊗[R f g z] B f g z →+* C f g z :=
  (Algebra.TensorProduct.lift (leftStalkHom f g z) (rightStalkHom f g z)
    (fun _ _ ↦ Commute.all _ _)).toRingHom
```

The auxiliary stalkAlgebra is the composite left stalk map. leftStalkHom and
rightStalkHom have the actual projection ring maps as data. stalk_square is proved
from pullback.condition and Scheme.Hom.stalkMap_congr_hom/stalkMap_comp;
rightStalkHom_commutes is its evaluation at a scalar. There are no postponed
obligations in this construction. tensorToStalk_tmul is reflexive,
tensorToStalk_spec proves both restrictions, and tensorToStalk_unique proves that
any map with those restrictions equals the constructed map. exists_tensorToStalk
keeps its signature and is now proved with this explicit witness.

All previously existing declaration signatures and the node's TeX statement are
unchanged. In particular the definitions tensorAlgebra, cohomologyModel,
stalkTensorComplex and IsComparisonIso now use the real canonical map. Any target
statement transitively using these definitions should be re-reviewed under stage
3 section 3; the proven restriction equations and uniqueness establish that the
intended mathematics has not changed. No Challenge declaration is modified.

## Users

The downstream scan listed 166 transitive importers. Its --uses scan found only
the item's own module mentioning tensorToStalk. No external proof uses the old
choice-based unfolding. The complete importer list is recorded below; all keep
the same signatures, ring map restrictions, and mathematical meaning. Claim
holders are the local snapshot when this record was written; none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison | Z2 | Explicit lift replaces chosen map; all original signatures preserved. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | B2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | C2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | D2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | P1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | P1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | N1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | A2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GenusInvariant | U2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | W2 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | F1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | V1 | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | Same canonical map; no source adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | none | Same canonical map; no source adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | Same canonical map; no source adaptation required. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | ORCHESTRA | Same canonical map; no source adaptation required. |
| TargetsCheck | none | Same canonical map; no source adaptation required. |
| WeilConjectures | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X2 | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | none | Same canonical map; no source adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | Same canonical map; no source adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Defs | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Inversion | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Perverse | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | Same canonical map; no source adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | Same canonical map; no source adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | Same canonical map; no source adaptation required. |

## Status

landed 20261012T135340-L-1703431 2026-10-12 (merge of deliver/Z2/Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison)
