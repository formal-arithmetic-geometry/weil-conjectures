# EtaleInverseLimitDescent public imports

## Reason

The supplied cone is already limiting. The proof uses a chart ring comparison based on
Mathlib's `isLimitOpensCone`, so the existence theorem
`AlgebraicGeometry.exists_limit_affine_transition` is not needed. Remove its public
module import rather than keeping an unused admitted dependency.

The theorem signature and all definitions used by targets are unchanged. The removed
module contains no instance or definition of its own, only that existence theorem.
`tools/downstream.py` found no downstream use of `exists_limit_affine_transition` or
`opensCone`; `tools/import_prune_check.py` passed. This delivery adapts no existing
module other than the item. The global build will check downstream elaboration.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

The import is removed. Statement imports are:

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
```

## Users

The following is the complete transitive downstream list reported by
`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.
No removed declaration occurs in any of these sources. Their statements keep their
meaning; no target review is reopened by a changed definition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit | B3 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit | E1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | R1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone | S2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | C2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | D2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | E2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | K1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes | M1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | R1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | ORCHESTRA | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity | T1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | R2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | C2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | E2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | H2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | Q2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | D2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.LimitPullbackSectionsColimit | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | ORCHESTRA | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | V2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | W2 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | R1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.EtaleFiniteDataDescent | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.FiniteHypercoverDescent | T1 | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.GabberCriterion | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.GaloisLisseRepresentations | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | No declaration or statement changes; no source use of the removed theorem. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | none | No declaration or statement changes; no source use of the removed theorem. |
| TargetsCheck | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | H1 | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X2 | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity | P1 | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.AffineSpace | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Defs | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Inversion | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Perverse | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Properties | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | No declaration or statement changes; no source use of the removed theorem. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | No declaration or statement changes; no source use of the removed theorem. |

## Status

landed 20261012T060752-L-2914545 2026-10-12 (merge of deliver/R2/Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent)
