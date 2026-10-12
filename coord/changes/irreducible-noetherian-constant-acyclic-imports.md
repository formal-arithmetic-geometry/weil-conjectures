# TopCat.irreducible_noetherian_constant_acyclic (import visibility)

## Reason

The theorem signature and all definitions are unchanged. The section-identification
lemma is used only by the proof, so its import must be non-public. The direct
Mathlib Flasque import is redundant because the newly used flasque-acyclicity
module imports it. Scratch compilation also shows that the first worker's AB
and GrothendieckAxioms.Sheaf proof imports are redundant, even when removed together.
This record documents only the resulting import interface change required by
stage-3 preflight; no target meaning or statement changes and no target semantic
review is reopened.

## Old

```lean
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import Sheaf.Topology.IrreducibleConstantSections
```

## New

```lean
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Topology.IrreducibleConstantSections
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Sheaf.Topology.FlasqueZariskiAcyclic
```

## Users

`tools/downstream.py Sheaf.Topology.IrreducibleNoetherianConstantAcyclic
--uses irreducible_constant_sections IsFlasque` lists 254 transitive importers
and finds no use of either removed public name among them. The sole direct
importer is `Sheaf.Topology.IrreducibleIntegerExtensionVanishing`: it uses this
module as a non-public proof import and applies only the unchanged acyclicity
theorem. Its whole source was read; it needs no adaptation. Consequently the
more distant importers do not receive the removed re-exports through it.
All their statements and definitions are unaffected. No claimed file is adapted.
Holding groups below are not needed for an adaptation and are left unspecified.

| module | group holding it | effect |
|---|---|---|
| Challenge | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ArtinSchreierSequence | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.BaseChangeCurve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.BrauerAlgebraicExtension | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseIrreducibleOpens | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.RetractAssertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparison | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCore | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCurve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.CurveCoefficientPair | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DerivedPullbackTorIndependentFlatComplex | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorModule | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.DivisorModuleLocal | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GenericRankLeadingDegree | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GenusInvariant | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.GmPicardPullback | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertDifference | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.IntersectionEffectiveCartier | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LocalDvrBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.LocallyFreeExtNaturality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Modules.VeryAmpleDisjointUnion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.Picard.InvertibleDirectImageClasses | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.PointTangentSeparationClosedImmersion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineDualityPairingNaturality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RationalSectionDivisor | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RationalSectionOrder | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeSerreVanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothProjectiveCurveConnected | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.TopDimensionalReductionIntersection | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ZariskiDimensionBound | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangeGeometricPoints | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.Paper.BaseChangeClosureComponents | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.Topology.IrreducibleIntegerExtensionVanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.Topology.NoetherianTopologicalCohomologyVanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| Sheaf.Topology.NoetherianVanishingByIrreducibleComponents | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| TargetsCheck | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.Projective | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Cohomology.Serre | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Assertions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.BoundaryNeighbourhood | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Modules.AffineHom | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Modules.Ample | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Degree | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.RationalPoint | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Representability | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryConstruction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LFunction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Defs | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Inversion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.FourierTransform.Properties.Stalk | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | not consulted (no adaptation) | unchanged statements and definitions; no adaptation |

## Status

landed 20261012T031733-L-1356556 2026-10-12 (merge of deliver/U1/Sheaf.Topology.IrreducibleNoetherianConstantAcyclic)
