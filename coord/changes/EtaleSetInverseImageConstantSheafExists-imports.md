# EtaleSetInverseImageConstantSheafExists public imports

## Reason

The former public import re-exported the composition-units theorem and its upstream
algebraic-structure modules, none of which the existence proof or signatures use.
Import the module defining `Scheme.etaleSetPullback` directly instead. This removes
unnecessary proof dependencies while preserving all three declarations exactly.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSheaves
```

## Users

`tools/downstream.py` lists the following transitive importers. The two direct importers
are `EtaleSetInverseImageConstantSheafUnique` and `EtaleSetInverseImageConstantSheaf`.
The uniqueness module uses only the unchanged Hom and Condition definitions and the
constant-sheaf/adjunction infrastructure re-exported by EtaleSheaves. The full constant-sheaf
module already publicly imports CompositionUnits itself. The three downstream modules
mentioning `etaleSetInverseImageCompositionUnits` each import CompositionUnits directly,
so that theorem stays available to them. This changes module re-exports only; it changes
no statement or definition, hence no target's mathematical meaning and no target review.
No adapted modules are needed.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | B3 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp` | G1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum` | R1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleFiniteStalkTests` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteSelection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | T1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | T1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | U1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl` | Q1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction` | M1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | P1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties` | D2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | N1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.RootTrivializationBaseChange` | P1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization` | A2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | X2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleGeometricPointSectionsStalkNatural` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafUnique` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.GenericFiniteLissePreservation` | J2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.GenericFinitePushforward` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.GenericFiniteSourceLisse` | J2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.GmPicardPullback` | R2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.IrreducibleLisseRefinement` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NormalGenericConstant` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NormalizedGenericDataCore` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.NormalizedGenericDataLifts` | M2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.ProperGeometricPointExchange` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant` | P2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantCounit` | R1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `TargetsCheck` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | A2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | C1 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.BaseChange.EtaleDerived` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | S2 | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.Integral.BaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | Declaration signatures and definition bodies unchanged; no adaptation required. |

## Status

landed 20261012T085333-L-37199 2026-10-12 (merge of deliver/S1/Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists)
