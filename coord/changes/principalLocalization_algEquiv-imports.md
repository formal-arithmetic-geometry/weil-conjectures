# Algebra.principalLocalization_algEquiv

## Reason

The algebra equivalence is valid for arbitrary polynomial relations and does not use the
relative complete-intersection definition. Remove that unused public import and supply only
Mathlib quotient operations and finite tuple operations. No declaration or target signature
changes. Both direct importers already publicly import the removed module on their own, so they
need no adaptation. All transitive users from tools/downstream.py are listed below.

## Old

```lean
public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
```

## New

```lean
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PrincipalLocalizationAlgEquiv | M2 | The theorem signature and meaning stay identical; the unused complete-intersection public import is replaced with the two Mathlib imports its statement needs. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.HenselianPairApproximation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuDesingularizeLiftingApply | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLiftOne | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLiftSmooth | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLiftSmoothSpecial | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLiftSolution | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLifting | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuLiftingWitness | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuReduceToField | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuResolveCharP | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuResolveSeparable | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuSmoothLiftModuloEight | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuSmoothLiftModuloEightAux | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PopescuSmoothing | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.PrincipalLocalizationCI | unclaimed | Unchanged source retains its own public complete-intersection import and imports this module only for its proof; no adaptation is needed. |
| Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPrincipalLocalization | unclaimed | Unchanged source compiled against the delivered module. It already publicly imports RelativeGlobalCompleteIntersectionPresentation itself and imports this module only for its proof. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| Sheaf.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| TargetsCheck | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unaffected: both direct importers retain their own public complete-intersection imports; its statements and public imports stay identical. |

## Status

landed 20261013T031545-L-3572132 2026-10-13 (merge of deliver/M2/Sheaf.RingTheory.PrincipalLocalizationAlgEquiv)
