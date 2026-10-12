# Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf: proof-local commands

## Reason

The static interface checker conservatively records every `open`, `variable`, and `omit`
command as an interface change, including commands confined to the private helper section.
This record documents those commands. No public declaration is added, no public import
changes, and neither original theorem signature changes. All helpers, including the
homology-comparison instance, are private. The proof-local variables end before the two
original public declarations. No target definition changes meaning; no target statement
review needs to be reopened.

## Old

The original module's opening commands, verbatim:

```lean
universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale
```

There were no private helper sections or their section variables.

## New

The replacement opening commands, verbatim:

```lean
universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale
```

Inside the namespace, the new `AbelianComparison` namespace contains a
`LocalComparison` section, `open Opposite`, and local variables for a site `C`, its
Grothendieck topology `J`, sheafification, the derived category, sheaf composition,
a complex `M`, and enough injectives. The `Key` subsection ends before adding the
enough-injectives variable; both sections and the helper namespace end before the
original public theorems. The `omit` commands only remove unused section instances
from private helper signatures. Every added declaration is private and fully proved.
These commands resolve notation, names, and section arguments in the private proofs;
they do not modify an existing definition or statement.

## Users

Read-only `tools/downstream.py` found 145 downstream modules. Its `--uses` search for
either existing theorem name found only the item itself, so no caller needs adaptation.
All downstream modules are listed conservatively below. Their statements and definitions
are unaffected because the public signatures and public imports are unchanged. None is
adapted in this delivery. Claim holders are read from this machine's claim records.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` | A3 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleColimitCocone` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | C2 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | D2 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | U1 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | E2 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula` | W2 | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.TorsionFilteredUnion` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` | unclaimed | No statement or definition changes; no adaptation needed. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No statement or definition changes; no adaptation needed. |
| `TargetsCheck` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | H1 | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.Reductions` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | X2 | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.ConstructibleSheaf.FinitePushforward` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Gabber` | Q2 | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No statement or definition changes; no adaptation needed. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No statement or definition changes; no adaptation needed. |

## Status

landed 20261012T060730-L-2903589 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf)
