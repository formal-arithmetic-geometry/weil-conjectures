# HenselianConnectedness proof-only direct-image import

## Reason

DirectImage.AffineMorphism supplies only the finiteness proof; no declaration signature
in HenselianConnectedness uses its API. Stage 3 requires proof-only imports to be plain.
This changes import visibility, not a theorem statement or a definition.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
```

## Users

The downstream.py transitive list has 205 modules. There are four direct importers:
Gabber, DegreeZero and HenselianClopenRestriction use plain proof imports and do not
re-export this module; WeilConjectures already explicitly public-imports the direct-image
module. No target statement or used definition changes; no target semantic review
is reopened. Unchanged scratch copies of all three proof importers compiled cleanly against
the delivered module overlay with lcompile.py. No module is adapted. Claim
holders below are the local snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | A2 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | V1 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No statement or definition changes. HenselianConnectedness is imported only for proofs, so its public imports were not re-exported here. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | E1 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| TargetsCheck | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures | unclaimed | API unchanged: already explicitly public-imports DirectImage.AffineMorphism (line 63). |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | B3 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | V2 | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No statement or definition changes. HenselianConnectedness is imported only for proofs, so its public imports were not re-exported here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.Gabber | M1 | No statement or definition changes. HenselianConnectedness is imported only for proofs, so its public imports were not re-exported here. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature or meaning changes; indirect dependency. The direct-import boundary preserves the public interfaces used here. |

## Status

landed 20261012T135231-L-1662598 2026-10-12 (merge of deliver/F1/WeilConjectures.AlgebraicGeometry.HenselianConnectedness)
