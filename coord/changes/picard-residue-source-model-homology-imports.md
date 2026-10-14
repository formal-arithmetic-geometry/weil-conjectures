# PicardResidueSourceModelHomology imports

## Reason

The homology model theorem does not use the explicit cycle/boundary quotient API.
Remove its public import of AffineResidueCycleHomology. The only direct importer,
PicardResidueHomologySourceResidueComparison, publicly imports that module itself,
so all transitive users retain the same available declarations through that importer.
No declaration signature or definition changes. No user requires adaptation.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
```

## New

The import is removed. All other existing public imports remain.

## Users

Computed with tools/downstream.py. Every downstream module reaches this item through
PicardResidueHomologySourceResidueComparison, which retains its own public import
of AffineResidueCycleHomology. Thus the public declarations available to every user
are preserved, including the target statements and their definitions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | N2 | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueChainComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueCycleComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardFixedModelResidueDerivedComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueCyclesGeometricNaturality | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturality | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged; quotient API retained by direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged; quotient API retained by direct importer. |
| TargetsCheck | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged; quotient API retained by direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged; quotient API retained by direct importer. |

## Status

landed 20261014T022551-L-4047783 2026-10-14 (merge of deliver/U1/Sheaf.AlgebraicGeometry.PicardResidueSourceModelHomology)
