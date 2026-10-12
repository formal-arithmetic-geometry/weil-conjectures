# fpqc_refinement_reflects_effectivity imports

## Reason

Remove a redundant public import. All of its exports remain publicly available through Mathlib.AlgebraicGeometry.Sites.Fpqc → Mathlib.AlgebraicGeometry.EffectiveEpi → Mathlib.AlgebraicGeometry.Morphisms.Flat → Mathlib.AlgebraicGeometry.Properties → Mathlib.AlgebraicGeometry.Limits. The proof compiles after removal. No declaration signature or definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Limits
```

## New

The direct import is removed; the retained public Fpqc import exports Limits transitively.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineFpqcDescent | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescent | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleEquivalenceH1 | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTorsorLifting | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTorsorReflection | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsDescent | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| TargetsCheck | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; no adaptation | Same public exports through Fpqc; statements and definitions unchanged. |

## Status

landed 20261012T112831-L-764873 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.FpqcRefinementReflectsEffectivity)
