# Sheaf.AlgebraicGeometry.SpecFieldPointResidueField public imports

## Reason

Remove redundant direct public imports. No declaration statement or definition
changes. Each removed module is still publicly reachable through the retained
Mathlib.AlgebraicGeometry.ResidueField import, along the following public chains:

- Mathlib.AlgebraicGeometry.ResidueField → Mathlib.AlgebraicGeometry.Stalk → Mathlib.AlgebraicGeometry.AffineScheme
- Mathlib.AlgebraicGeometry.ResidueField → Mathlib.AlgebraicGeometry.Stalk → Mathlib.AlgebraicGeometry.Morphisms.Preimmersion → Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks → Mathlib.RingTheory.Spectrum.Prime.TensorProduct → Mathlib.RingTheory.Spectrum.Prime.Topology → Mathlib.RingTheory.Spectrum.Maximal.Localization → Mathlib.RingTheory.Spectrum.Prime.RingHom → Mathlib.RingTheory.LocalRing.ResidueField.Ideal

This structural public-import check applies to every downstream module: all
previously exposed declarations and instances remain available with their exact
original types. Therefore no target meaning changes or target review reopens,
and no importing module needs adaptation. The final item compiles unchanged in
its statements and with both new proofs using only the retained import.

## Old

```lean
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
```

## New

```lean
public import Mathlib.AlgebraicGeometry.ResidueField
```

## Users

The following is the complete transitive downstream list from the read-only
source import graph (`tools/downstream.py` / `leanindex.downstream`). Group
holding an item is taken from the local claim record when present.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | R1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitFactorization | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant | B2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFilteredData | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | B3 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism | U1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | N2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSheafGeneration | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | C2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | U2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | D2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility | V1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | N1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineCoverStratification | T1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFibreSpecialization | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints | E2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible | U1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSeparatedStratifiedFinite | G2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleStratifiedFinite | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FibreProductPointResidueField | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceData | S2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant | Y2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTrace | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists | B3 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleYonedaLocalTrivializations | Q1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePiecePersistence | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocalReduction | R2 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatFpLqfBoundedStratification | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatQuasiFiniteStratification | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | H1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | J1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | K1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition | K1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantRetraction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | C1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleEtaleLocalSplit | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension | Q1 | Same public declarations and types via transitive imports; no adaptation. |
| TargetsCheck | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | T2 | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X2 | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | K1 | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Defs | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none recorded | Same public declarations and types via transitive imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none recorded | Same public declarations and types via transitive imports; no adaptation. |

## Status

landed 20261012T060741-L-2909106 2026-10-12 (merge of deliver/J1/Sheaf.AlgebraicGeometry.SpecFieldPointResidueField)
