# Sheaf.Paper.FlatLocalCriterionNonzerodivisor imports

## Reason

The upstream filtration theorem is used only in the proof. Replace its public import
with a plain import and explicitly expose the Mathlib modules needed by the unchanged
signature: flatness, the quotient-module instance, the maximal ideal and QuotSMulTop.
Noetherian definitions are already exported by Torsion.Basic and Flat.Basic.
The local-ring homomorphism lemmas are imported only for the proof.
The `open scoped Pointwise` command enables notation used in the proof and adds no definitions.

## Old

```lean
public import WeilConjectures.Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.QuotSMulTop
```

## New

```lean
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import WeilConjectures.Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.LocalRing.RingHom.Basic
```

The theorem signature remains byte-for-byte identical; no definition is changed.

## Users

The only direct importer imports the item privately and already imports its own public
signature dependencies. It is compiled unchanged against the new module. All transitive
users below therefore retain the same declarations, hypotheses and conclusions. No
adaptation is needed. Holdings are the read-only repository snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.Paper.GaloisLisseRepresentations | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.CompleteLocalMapCohenPresentation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.CompleteLocalMapRegularPresentation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.ExistsCompleteLocalFlatPresentation | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FiniteTypeGRing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FiniteTypeGRingAux | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FiniteTypeIntGRing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FlatOverRegular | unclaimed | Direct importer: compiles unchanged against the delivered module. |
| Sheaf.RingTheory.FormallySmoothAdicClosedFiber | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothAdicFlat | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothAdicLift | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothCompleteLocalGenericFiber | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothCompleteLocalRegular | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FormallySmoothRegularCompleteFiniteFieldRegular | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FsAdicClosedFiberModel | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.FsAdicLiftOverFiniteCoefficientMap | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.GeometricallyRegularOverFieldFlat | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.MiracleFlatness | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PolynomialFormalFiber | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PolynomialFormalFiberGeometric | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PolynomialGRingComparison | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuCharPPreparation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuCharPPreparationCore | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuCharPPreparationGlobal | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuEnlargeSolutionModulo | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuFlatCoordinates | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalFlatFiberData | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuParameterQuotientLocalResolution | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuSeparableParameterQuotient | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.PopescuSolutionModulo | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| TargetsCheck | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unknown | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer: theorem and all definitions unchanged; no semantic change. |

## Status

landed 20261012T210030-L-953939 2026-10-12 (merge of deliver/V3/Sheaf.Paper.FlatLocalCriterionNonzerodivisor)
