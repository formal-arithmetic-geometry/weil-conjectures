# CategoryTheory.brownRepresentabilityRightAdjoint opposite scope

## Reason

The proof uses Mathlib's scoped opposite triangulated structures. Opening
CategoryTheory.Pretriangulated.Opposite enables precisely those instances. The
preflight conservatively treats an added open command as an interface change.
No public signature, definition, notation, attribute, or target statement changes.
All added imports are proof-only. This command is the only existing interface
change identified by preflight; the new module is separately reviewed as a new node.

## Old

```lean
open CategoryTheory.Limits
```

## New

```lean
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite
```

## Users

No existing declaration type or definition changes, so all downstream statements
retain their meanings and there is no semantic target review to reopen. No module
besides the item is adapted. The new helper's statement uses the canonical opposite
triangulated structure exported by Mathlib.Triangulated.Yoneda, and the same scope
is required in the proof to match it. The table includes every transitive importer
reported by leanindex.downstream, the implementation used by tools/downstream.py.
Claim holders are recorded from the read-only local snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint | E2 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | P1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | A2 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | H2 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | Q2 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GenusInvariant | U2 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | A3 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperUpperShriekComposition | E1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | F1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | V1 | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | No statement or definition changes; no adaptation required. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | none | No statement or definition changes; no adaptation required. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | No statement or definition changes; no adaptation required. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | ORCHESTRA | No statement or definition changes; no adaptation required. |
| TargetsCheck | none | No statement or definition changes; no adaptation required. |
| WeilConjectures | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Defs | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Inversion | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Perverse | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | No statement or definition changes; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | No statement or definition changes; no adaptation required. |

## Status

landed 20261012T085229-L-10437 2026-10-12 (merge of deliver/E2/Sheaf.CategoryTheory.BrownRepresentabilityRightAdjoint)
