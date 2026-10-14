# SectionRingVeroneseFractionsCore imports

## Reason

Remove three redundant direct public imports. No declaration signature or definition
changes. The retained kernel module publicly imports the numerator-map module and
section-fraction presentation; the numerator-map module publicly imports the section
ring and homogeneous localization. Thus all previously public declarations remain
public through exactly those paths. No proof-only import is made public.

## Old

```lean
public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel
public import Sheaf.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
```

## New

```lean
public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore --names` lists the
following modules. The common effect is justified by the unchanged public transitive
closure described above; neither statements nor their meanings change in any user.
The direct importer, `SectionRingVeroneseFractions`, also independently imports all
three removed imports. No forced adaptations are necessary. No target definition
changes, so target meaning review is not reopened.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjChartFormula` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjCompatibleCharts` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjLocalChart` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjOpen` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperProjective` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.DimOneQuasiProjective` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.GluedComponentAffineSection` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientData` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientHom` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientNumerator` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingSingleQuotientChart` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `TargetsCheck` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | claim present; see coord/claims | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | Unchanged declarations and transitive public availability; no adaptation. |

## Status

landed 20261014T020512-L-3811609 2026-10-14 (merge of deliver/H2/Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore)
