# UnramifiedQuasiFinite imports

## Reason

Second reading found the public import of Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
unused by both the statement and proof. The smaller import set compiles and the proved
theorem has only propext, Classical.choice and Quot.sound. No declaration changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
```

## New

The unused import is removed. All existing declaration signatures remain byte for byte
unchanged. The remaining public imports are OpenImmersion and QuasiFiniteMorphism;
the added proof-only imports are FormallyUnramified and Unramified.LocalStructure.

## Users

Ran tools/downstream.py Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite --uses
LocallyQuasiFinite: 202 downstream modules and zero occurrences of that Mathlib
predicate. The two direct importers, EtaleSeparatedStratifiedFinite and
UnramifiedOverFieldDiscrete, import this module privately (plain import), so this
change does not alter their public interfaces or the interfaces of further users.
Read both direct importers: they use the unchanged project theorem and project
quasi-finiteness predicates, and no declaration from the removed Mathlib module.
No adaptation of a claimed module is needed; no statement or definition becomes
stronger, weaker or different, and no target semantic review is reopened.
The group-holding column is not applicable: none of these users is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceData | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleTrace | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.UnramifiedFibrePointIsolated | not adapted | no statement or definition change |
| Sheaf.AlgebraicGeometry.UnramifiedOverFieldDiscrete | not adapted | no statement or definition change |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | not adapted | no statement or definition change |
| Sheaf.ConstructibleSheaf.LocallyConstantRetraction | not adapted | no statement or definition change |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | not adapted | no statement or definition change |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | not adapted | no statement or definition change |
| Sheaf.Paper.FiniteEtaleEtaleLocalSplit | not adapted | no statement or definition change |
| Sheaf.Paper.GaloisLisseRepresentations | not adapted | no statement or definition change |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not adapted | no statement or definition change |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not adapted | no statement or definition change |
| TargetsCheck | not adapted | no statement or definition change |
| WeilConjectures | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | not adapted | no statement or definition change |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | not adapted | no statement or definition change |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | not adapted | no statement or definition change |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | no statement or definition change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Defs | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Inversion | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Perverse | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Properties | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | no statement or definition change |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Gabber | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | no statement or definition change |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | no statement or definition change |

## Status

landed 20261012T063506-L-3153609 2026-10-12 (merge of deliver/D2/Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite)
