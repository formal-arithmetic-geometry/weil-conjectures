# sectionRing_veronese_fraction_core

## Reason

Upstream review #1428 identified the old conclusion `Nonempty (_ ≃+ _)` as
weakened: it did not state that the canonical map on fraction classes is
bijective. The canonical map `[n, ξ] ↦ ξ / s^n` is the inverse of the explicit
quotient equivalence `sectionRingVeroneseFractionEquiv`; the theorem now states
bijectivity of that map directly. This is a statement correction and requires
review of its downstream users, but no downstream signature uses the old
`Nonempty` conclusion.

## Old

```lean
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Nonempty (HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
```

## New

```lean
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective
      (sectionRingVeroneseFractionCanonicalMap X L d s)
```

The public definition is
`sectionRingVeroneseFractionCanonicalMap X L d s :=
(sectionRingVeroneseFractionEquiv X L d s).symm.toAddMonoidHom`.
It has domain `SectionFractionPresentation` and codomain
`HomogeneousLocalization.Away`; on the class represented by a degree-`n`
numerator it is the fraction with denominator `s^n`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleProjChartFormula` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleProjCompatibleCharts` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleProjLocalChart` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.AmpleProjOpen` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ProperProjective` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.DimOneQuasiProjective` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.GluedComponentAffineSection` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientData` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientHom` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingCoefficientNumerator` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingSingleQuotientChart` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `TargetsCheck` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore (1)` | unclaimed | Its imports expose the repaired theorem; no signature adaptation is required. |

## Status

landed 20261013T201809-L-3977060 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore)
