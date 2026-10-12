# SeparatedOpenInduction imports

## Reason

Remove redundant direct public imports. The remaining public import Separated
imports ClosedImmersion, which imports Affine, which publicly imports
QuasiSeparated, which publicly imports QuasiCompact. Thus the two removed
modules are still public transitive imports. No declaration, instance, notation,
or definition used by a downstream statement is removed or changed.
The theorem signature is byte-for-byte identical; no target meaning changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
```

## Users

The following exhaustive transitive list is from
`tools/downstream.py Sheaf.AlgebraicGeometry.SeparatedOpenInduction --uses separated_quasiCompact_open_induction`.
The same transitive export argument applies to each; no sources are adapted.
The only direct importers are QuasiCompactOpenInduction and
QuasiCompactOpenIntersectionProperty, and both import this module privately.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedCounitHomologyFactorization | M2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization | U3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedConcentration | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineKoszulCechDerivedComparison | Z2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectMapLift | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectPlusShift | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | N2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine | S1 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleProjLocalChart | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleProjOpen | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | J3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | P2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperProjective | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DQCoheratorAdjunction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohCompactGeneration | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedQCohPerfectGeneration | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | Q2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | P2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | N3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | R3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.GluedComponentAffineSection | H2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.InvertSCOhomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality | V1 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | V2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | S3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomGap | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | Q2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectIntoSupportPowerTorsion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectSupportedMapLift | E3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | Q1 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | A3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | V3 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperPerfectRightAdjointCoproducts | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentSupportAnnihilation | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsDerivedDirectImageRightAdjoint | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty | J1 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeSerreVanishing | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointOpenSupportCriterion | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | Z2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | Z2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift | P1 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLocus | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedDerivedGeneratedPerfect | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffine | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction | X2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectDetectorGluing | B2 | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedPerfectGenerator | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparison | unclaimed | Same public declarations via Separated; no adaptation. |
| Sheaf.Paper.QCohAcyclicDerivedSectionsComparisonSections | Y2 | Same public declarations via Separated; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Same public declarations via Separated; no adaptation. |
| TargetsCheck | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.Projective | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same public declarations via Separated; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same public declarations via Separated; no adaptation. |

## Status

landed 20261012T150949-L-2229206 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.SeparatedOpenInduction)
