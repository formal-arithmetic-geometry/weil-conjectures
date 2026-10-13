# CyclicExtensionFlatDescentImports

## Reason

Second reading found that `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` is unused:
the statement uses `Function.Exact`, already available from the remaining public
Mathlib imports, and no short-complex declaration occurs in the proof. Remove this
public import rather than exporting a proof-plan convenience. Also remove the
redundant private imports `Mathlib.LinearAlgebra.Quotient.Basic` and
`Mathlib.LinearAlgebra.Prod`, already available through the statement imports.
The theorem signature is byte-for-byte unchanged. No definition changes.

## Old

```lean
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
```

## New

```lean
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
```

## Users

The sole direct importer is `Sheaf.RingTheory.TorsionExtensionFlatDescent`, held by
R1 at review time. Its original source compiles unchanged using the edited sandbox
module through `lcompile.py`; no forced adaptation is required. Its import of
`CyclicExtensionFlatDescent` is private, so the removed re-export cannot affect
visibility in the transitive importers. All modules reported by
`tools/downstream.py Sheaf.RingTheory.CyclicExtensionFlatDescent --uses
exists_cyclic_extension_flat_descent` are listed below. No target meaning changes
and no target statement review reopens.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckDevissageRecoverLevels | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceDevissage | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionControlledAffineAlgebraization | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionControlledAffineCandidate | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionControlledEasyAlgebraizationBridge | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | S1 | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.RingTheory.FormalGlueingEquivalence | J3 | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.RingTheory.FormalGlueingIsogeny | H2 | No signature or meaning change; the direct importer imports this module privately. |
| Sheaf.RingTheory.TorsionExtensionFlatDescent | R1 | Original compiled unchanged against the edited module; no signature or meaning change. |
| TargetsCheck | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No signature or meaning change; the direct importer imports this module privately. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No signature or meaning change; the direct importer imports this module privately. |

## Status

landed 20261013T100036-L-2471262 2026-10-13 (merge of deliver/M4/Sheaf.RingTheory.CyclicExtensionFlatDescent)
