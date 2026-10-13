# strictLocalFibreRestriction_compatibility import pruning

## Reason

Remove the unused public BaseChange.GlobalSections import. The data definition
uses globalSectionsUpperStarMap from the narrower UpperLowerStar.GlobalSections,
already publicly available through QcqsStrictLocalModuleComparison. The new proof
uses StrictLocalSectionPullback privately. No signature, definition, target meaning,
or visibility of a declaration changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
```

## New

```lean
public import Sheaf.AlgebraicGeometry.GeometricFibreExchangeGerms
public import Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import Sheaf.AlgebraicGeometry.StrictLocalSectionPullback
```

## Users

The sole direct importer is `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux`.
IntegralStrictHenselianGeometricFibreSections imports BaseChange.GlobalSections privately, so it does not re-export those declarations. IntegralFibreSectionLocalLiftAux compiles against the pruned module without them; no adaptation is needed.
It does not publicly import this item, so this item's removed re-export does not
propagate to its public users. All transitive downstream modules retain their
statements, definitions, and proof imports. No adaptation or target statement review
is needed. The textual uses of strictLocalFibreRestriction_compatibility are the item
and that sole direct importer. The full downstream list follows, with local claim
holders; no listed module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged; no adaptation needed |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged; no adaptation needed |
| TargetsCheck | unclaimed | unchanged; no adaptation needed |
| WeilConjectures | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged; no adaptation needed |

## Status

landed 20261013T054212-L-441543 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.StrictLocalFibreRestrictionCompatibility)
