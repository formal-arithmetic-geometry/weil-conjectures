# CategoryTheory.colimitSite_sections_bijective / colimitSite_sections_isIso

## Reason

Both unchanged signatures are specializations of SiteFilteredColimitSections.
ColimitSites supplies no theorem used in either proof. Replace its public import by
Mathlib imports supplying the Cat and Under types appearing in the signatures.
No declaration, definition or target signature changes.

## Old

```lean
public import Sheaf.CategoryTheory.ColimitSites
public import Sheaf.CategoryTheory.SiteFilteredColimitSections
```

## New

```lean
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Sheaf.CategoryTheory.SiteFilteredColimitSections
import Mathlib.CategoryTheory.Filtered.Final
```

## Users

The three direct importers import this module only for proofs, so the removal does
not affect any downstream public signature. CohomologyColimitSites and
ColimitSiteCechComplex also import ColimitSites explicitly. The definitions in this
module's signatures remain public through the listed Mathlib imports. No adapter
modules are required. The table lists the complete transitive downstream set from
tools/downstream.py, including source-library and target aggregator modules.
The maintainer's global build remains the verification of all downstream modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.CofilteredEtaleCohomologyCocone | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNoetherianDescent | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleCohomologyLocalRingColimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationPullback | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.LimitPullbackSectionsColimit | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.CategoryTheory.CohomologyColimitSites | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.CategoryTheory.ColimitSiteCechComplex | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.Paper.GabberCriterion | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged; no adaptation | signatures unchanged; import pruning only |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | unchanged; no adaptation | signatures unchanged; import pruning only |
| TargetsCheck | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.AffineSpace | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Defs | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Inversion | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Perverse | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Properties | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Gabber | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged; no adaptation | signatures unchanged; import pruning only |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged; no adaptation | signatures unchanged; import pruning only |

## Status

landed 20261012T044747-L-2036570 2026-10-12 (merge of deliver/K1/Sheaf.CategoryTheory.ColimitSiteSections)
