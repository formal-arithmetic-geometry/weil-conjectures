# RootLiftingEtaleRetraction import visibility

## Reason

`Mathlib.RingTheory.Henselian` supplies only the simple-root uniqueness theorem used
in the proof. The signature's polynomial and local-ring residue-field notions are
already exposed by the two retained public imports. A scratch copy compiles with
Henselian as a plain import and the redundant quotient-operations import removed.
No statement, definition, or target meaning changes; no semantic review is reopened.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Henselian
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure
```

## Users

`tools/downstream.py Sheaf.RingTheory.RootLiftingEtaleRetraction --uses
HenselianLocalRing HenselianRing eq_of_eval_eq_zero_of_not_isUnit_sub` lists 158
transitive importers. Its sole direct importer is
`Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`, whose whole source was read.
It imports this module only for proofs and independently publicly imports
`WeilConjectures.Mathlib.RingTheory.Henselian`, which publicly imports Mathlib's
Henselian module. Thus every re-export removed here remains available there and
throughout the downstream closure. All six downstream name hits retain that route;
none uses the simple-root uniqueness name. No claimed module requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ClosedPointSheafApproximation | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.GeometricStalkSupport | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk | X2 | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.GabberCriterion | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.StrictlyHenselianEtaleAcyclic | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.ZeroDimensionalCohomology | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| Sheaf.Paper.ZeroDimensionalGlobalSectionsExact | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| TargetsCheck | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.AffineSpace | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Defs | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Inversion | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Perverse | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Properties | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Properties.BaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.FourierTransform.Properties.Stalk | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Gabber | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not consulted (no adaptation) | unaffected; Henselian has an independent public import at the sole direct importer |

## Status

landed 20261012T044800-L-2044110 2026-10-12 (merge of deliver/Y2/Sheaf.RingTheory.RootLiftingEtaleRetraction)
