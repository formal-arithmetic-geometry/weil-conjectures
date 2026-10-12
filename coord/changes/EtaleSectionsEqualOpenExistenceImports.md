# AlgebraicGeometry.exists_etaleSections_equal_open

## Reason

The completed proof handles both implications through geometric stalks and does not use
the inverse-image composition comparison. Export only the module needed for the unchanged
statement's set inverse image. Import pruning was checked against the library sources.
No declaration signature or definition changes. All downstream modules are listed below
as a conservative superset of the users affected by the public import change.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSheaves
```

`EtaleSheaves` already publicly exports `UpperLowerStar.Defs` through `ConstructibleSheaf.Defs`.
The only downstream textual user of `etaleSetInverseImageCompositionUnits`,
`Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent`, imports its module publicly itself.
The direct importer `Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen` likewise publicly imports
that module. Thus no downstream source adaptation is required. The static import pruning
check passed, including declarations formerly reachable through the removed import.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | G1 | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| TargetsCheck | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | No signatures change; imports needed by existing declarations remain available. |

## Status

landed 20261012T112830-L-764194 2026-10-12 (merge of deliver/B2/Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpenExistence)
