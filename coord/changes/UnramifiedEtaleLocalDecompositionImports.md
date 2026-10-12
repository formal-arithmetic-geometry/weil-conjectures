# exists_etale_closed_immersion_decomposition_of_unramified_at_points

## Reason
Remove redundant public imports while minimizing the repaired module's imports. No existing declaration, signature, definition, instance or notation changes. Mathlib.AlgebraicGeometry.Morphisms.Etale publicly imports FormallyUnramified, which publicly imports Proper, which publicly imports Separated and Finite. Pullbacks is already a public transitive import of these modules. Thus the same modules and declarations remain publicly reachable; this is an import-list cleanup, with no target requiring statement review. The new helper modules are plain proof imports.

## Old
```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
```

## New
```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
```

## Users
The read-only downstream scan listed the following modules. All retain the same transitive public imports and theorem signature, so no adaptation is required. FiniteUnramifiedEtaleLocalReduction is the sole direct user of the theorem declaration; its application is unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceData | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleTrace | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.ConstructibleSheaf.LocallyConstantRetraction | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.Paper.FiniteEtaleEtaleLocalSplit | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.Paper.GaloisLisseRepresentations | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unchanged; not adapted | same transitive public imports and declaration signature |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; not adapted | same transitive public imports and declaration signature |
| TargetsCheck | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Defs | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Inversion | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Perverse | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Properties | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Gabber | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; not adapted | same transitive public imports and declaration signature |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; not adapted | same transitive public imports and declaration signature |

## Status
landed 20261012T063513-L-3156682 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition)
