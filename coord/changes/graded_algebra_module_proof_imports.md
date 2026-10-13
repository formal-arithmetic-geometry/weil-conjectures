# AlgebraicGeometry.exists_finiteType_graded_algebra_module

## Reason

Mathlib.AlgebraicGeometry.Morphisms.Affine is needed only by the proof; the signature
needs Mathlib.AlgebraicGeometry.Pullbacks. Narrow its public import to Pullbacks.
The sole direct importer, Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange, already
publicly imports Mathlib.AlgebraicGeometry.Morphisms.Affine independently, so this
narrowing removes no API from that importer or any of its descendants. The theorem's
signature, definitions and meaning are unchanged. No target statement or definition
needs renewed mathematical review and no module adaptation is required.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Pullbacks
```

Affine proof declarations are available through the plain AffineModuleCorrespondence
import. The existing theorem signature and docstring are byte-for-byte unchanged.

## Users

The following is the full downstream list from tools/downstream.py. The declaration
usage search additionally finds only the item itself and GradedModuleAffineBaseChange.
No user statement changes, and no other held module is edited. An unchanged scratch
copy of the direct importer compiled against the final module overlay in 45.4 seconds
without errors or warnings. This scratch copy is not delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCompactificationData | B2 | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCore | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationCoreCandidate | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ChowAlgebraizationData | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ChowPullbackAlgebraization | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChange | unclaimed | Existing direct public Affine import retains all affine API; statement unchanged. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceMaximalFailure | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjectivePullback | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.AlgebraicGeometry.VanishingProjective | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraLift | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | E3 | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| TargetsCheck | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Affine API still exported by the direct importer; declarations unchanged. |

## Status

landed 20261013T054241-L-450389 2026-10-13 (merge of deliver/U1/Sheaf.AlgebraicGeometry.GradedModuleAffineBaseChangeAlgebra)
