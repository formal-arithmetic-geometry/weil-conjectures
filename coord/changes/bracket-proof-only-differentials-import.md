# Bracket proof-only differentials import

## Reason

The local presheaf-differentials extension declares only `postcomp_comp` and
`Universal.desc_comp`. Bracket uses the latter only inside a proof; its signatures
use the underlying Mathlib definitions already available from InfPointsEquiv.
The stage-3 import rule requires this extension to be imported without `public`.
Preflight requires a change record for removing any public import.

## Old

```lean
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
```

## New

```lean
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
```

## Users

`tools/downstream.py Bracket --uses PresheafOfModules.Derivation.Universal.desc_comp
PresheafOfModules.Derivation.postcomp_comp` found 186 downstream modules, none
using either extension lemma. A whole-library textual search likewise finds no
users outside Bracket and the extension itself. The umbrella WeilConjectures
imports the extension directly as well. Thus no downstream adaptation is needed;
no statement or definition changes meaning and no target review is reopened.
The table lists all downstream modules and the edited module. Groups are the
local claim snapshot; no other module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket | F2 | proof-only import; signatures unchanged |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | F1 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | U2 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | R2 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | K1 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | M1 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.MixedCommutatorTangent | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | Q1 | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed locally | none; no use of removed reexports |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed locally | none; no use of removed reexports |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed locally | none; no use of removed reexports |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed locally | none; no use of removed reexports |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed locally | none; no use of removed reexports |
| Sheaf.Paper.IntegralCoverTrivialCohomology | T2 | none; no use of removed reexports |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed locally | none; no use of removed reexports |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed locally | none; no use of removed reexports |
| TargetsCheck | unclaimed locally | none; no use of removed reexports |
| WeilConjectures | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | H1 | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | Q2 | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Image | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field | G2 | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring | M2 | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | G1 | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.RankOne | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Defs | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Inversion | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Perverse | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Properties | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | T1 | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed locally | none; no use of removed reexports |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed locally | none; no use of removed reexports |

## Status

landed 20261012T044743-L-2034714 2026-10-12 (merge of deliver/F2/WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket)
