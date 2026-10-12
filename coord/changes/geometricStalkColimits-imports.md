# geometricStalk_preservesColimits imports

## Reason

The signature needs EtalePoint and Additive. Skyscraper and
HomologicalComplexAbelian supply proof instances and should be private imports.
EtaleSheaves is unused. No declaration signature or definition changes.
The sole direct importer, TorsionSheafCharacterizations, imports this item
privately and does not use the removed public exports. Its own public imports
supply its signature vocabulary, and its two theorem proofs remain sorry.
Consequently none of the transitive users changes meaning or requires adaptation,
and no target review is reopened. The table lists all modules reported by
`tools/downstream.py Sheaf.AlgebraicGeometry.GeometricStalkColimits`.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Sheaf.AlgebraicGeometry.EtaleSheaves
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | F1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | J2 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | S2 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | G1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | U2 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | Q1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations | W2 | Private direct import only; signatures use its own public imports; proofs remain sorry. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| TargetsCheck | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | H1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | Q2 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | T1 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No effect: sole direct importer imports the item privately, so its exports are unchanged. |

No other modules are adapted in this delivery; group ownership is immaterial to
this source-only verification because no files belonging to those groups change.

## Status

landed 20261012T041234-L-1711133 2026-10-12 (merge of deliver/S2/Sheaf.AlgebraicGeometry.GeometricStalkColimits)
