# GradedNakayamaFree imports

## Reason

Second reading corrects the proof-only public import of MinimalPresentationTor and removes
redundant explicit ModuleCat.Basic and Quotient.Basic imports. The target signature uses
ModuleCat, the Tor category instances, direct sums, homogeneous elements and module bases;
its explicit public Mathlib imports still provide all of these. The presentation/Tor
calculation and quotient manipulations are needed only inside the proof and remain available
through private imports. The earlier worker also pruned the proof-only twisting-sheaf import
and added private construction and finiteness imports. No declaration signature or definition
changes, and no target meaning changes or target semantic re-review is required.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Sheaf.RingTheory.MinimalPresentationTor
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.RingTheory.GradedKernelFinite
import Sheaf.RingTheory.GradedNakayamaGeneration
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
```

## New

```lean
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.RingTheory.MinimalPresentationTor
import Sheaf.RingTheory.GradedKernelFinite
import Sheaf.RingTheory.GradedNakayamaGeneration
import Sheaf.RingTheory.MinimalGradedPresentationExists
import Mathlib.RingTheory.Finiteness.Basic
```

## Users

Read-only `tools/downstream.py Sheaf.RingTheory.GradedNakayamaFree --uses
graded_nakayama_free MinimalGradedPresentation exists_minimalPresentationTor_equiv` lists
182 downstream modules. There is exactly one direct importer, GradedSyzygy; its import is
private. It explicitly imports ModuleCat.Basic, does not use the minimal-presentation
structure or calculation, and its unchanged source compiles against the corrected sandbox
module (1.9 seconds, no warnings). Other modules receive no re-export of GradedNakayamaFree
through this private boundary. None needs adaptation. No current claim-holder records are
available in this read-only clone; no other group's files are edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GenusInvariant | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| Sheaf.RingTheory.GradedSyzygy | not recorded in clone | Direct private importer; unchanged source compiled; no adaptation or statement effect. |
| TargetsCheck | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.AffineSpace | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Defs | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Inversion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Perverse | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Properties | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.FourierTransform.Properties.Stalk | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not recorded in clone | Indirect through private GradedSyzygy import; no adaptation or statement effect. |

## Status

landed 20261012T121039-L-988448 2026-10-12 (merge of deliver/P2/Sheaf.RingTheory.GradedNakayamaFree)
