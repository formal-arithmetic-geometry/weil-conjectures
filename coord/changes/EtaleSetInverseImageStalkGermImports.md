# EtaleSetInverseImageStalkGerm public imports

## Reason

The completed proof uses the general point-comparison isomorphism for set coefficients.
The composition-units theorem is unnecessary for this proof. Import the smaller
`EtaleSheaves` module for the statement's `Scheme.etaleSetPullback` definition, and import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` only for the proof.
No statement or definition changes; no target interpretation changes or requires reopening.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm --uses
etaleSetInverseImageStalkGerm` lists 153 downstream modules and no occurrence of the
changed module's theorem in them. All five direct importers were read: each independently
imports `EtaleSetInverseImageCompositionUnits` (publicly in four, privately in
`FinitePushforwardSetStalk`). Thus no direct importer loses a declaration it previously
obtained from this module. Their public interfaces are preserved, so their transitive
importers also require no adaptation. No other module is edited or needs to be claimed.
The table includes the full downstream list; group claims are immaterial because no
changes to their files are required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant | not modified | No adaptation; independently imports CompositionUnits. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleSectionsEqualOpen | not modified | No adaptation; independently imports CompositionUnits. |
| Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | not modified | No adaptation; independently imports CompositionUnits. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | not modified | No adaptation; independently imports CompositionUnits. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | not modified | No adaptation; independently imports CompositionUnits. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not modified | No adaptation; direct importers retain their interfaces. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not modified | No adaptation; direct importers retain their interfaces. |
| TargetsCheck | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.AffineSpace | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Defs | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Inversion | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Perverse | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Properties | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.FourierTransform.Properties.Stalk | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Gabber | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not modified | No adaptation; direct importers retain their interfaces. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not modified | No adaptation; direct importers retain their interfaces. |

## Status

landed 20261012T053919-L-2629415 2026-10-12 (merge of deliver/B2/Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm)
