# coherentFormalModules_closedUnderFiniteProducts imports

## Reason

`Mathlib.CategoryTheory.Preadditive.FunctorCategory` is not needed by the statement
or proof of finite-product closure. Remove this redundant public import. The
only direct importer, `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`,
already publicly imports FunctorCategory itself. Thus it loses no available
instance or declaration, and its own public interface stays the same. Every
further downstream module receives the same public imports through this direct
importer. No target statement, definition, or existing signature changes.
No module is adapted or delivered beyond the item and the two new nodes.

## Old

```lean
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
```

## New

The redundant import is removed from CoherentFormalModulesFiniteProducts.
The new empty-product proof uses IsZero.obj and also needs no import of this module.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoherentFormalModulesFiniteProducts
--uses coherentFormalModules_closedUnderFiniteProducts` was run. It found one
direct declaration user, CoherentFormalModulesAbelian, and 176 transitive
importers; all are listed below. That direct importer already imports the removed
module explicitly. No elaborated statement or definition can change through
this removal, since the remaining direct importer retains exactly that module.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleEpi | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.CoherentFormalShortExactLevels | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FormalCompletionExact | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FormalSystemsProperSupportSerre | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystem | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.GaloisLisseRepresentations | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| TargetsCheck | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | claimed (see claim record) | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration changes; direct importer imports FunctorCategory itself. |

## Status

landed 20261012T220528-L-1396208 2026-10-12 (merge of deliver/V3/Sheaf.AlgebraicGeometry.CoherentFormalModulesFiniteProducts)
