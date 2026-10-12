# Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient

## Reason

The ideal-integrality result is used only in the proof. Its import must be private.
Expose the signature's dependencies explicitly: integral algebra definitions,
polynomial evaluation, ideal maps, quotient definitions, and idempotent elements.
No declaration signature, definition, or target meaning changes.

## Old

```lean
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Group.Idempotent
```

## New

```lean
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Group.Idempotent
```

## Users

`tools/downstream.py Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial
--uses Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient`
reports 274 transitive importers. The only direct importer and the only downstream
textual user of the declaration is `Sheaf.RingTheory.LiftIdempotentUpstairs`.
It imports the item privately and uses its unchanged theorem. A scratch copy
of the revised item and that importer compiled together through `lcompile.py --all`
without warnings, checking the importer against the revised compiled item.
Because that import is private, it does not re-export the item's former public
imports to its downstream modules. Their public interfaces and statement meanings
are therefore unaffected. No importer is edited or adapted. No target definition
changes, so no target statement review is reopened. The rows below enumerate the
full transitive list, including modules which do not mention the theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianNeighborhoodColimit | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.AffineClosedHenselianRingPresentation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FinitePushforwardSetStalkAux | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentEqualizer | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberH0EtaleInjective | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteLift | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteSection | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberH0ProjectionRestrictions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberQuotientLocalizations | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.IntegralPointedClopenRefinement | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.LiftProjectiveModuleEtale | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.Paper.GaloisLisseRepresentations | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.Paper.SmoothSectionEtaleLift | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.EtaleSectionLiftingOfGabberRoots | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.EtaleTripleStrictHenselizationIdentification | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FactorizationLocallyNilpotent | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FilteredColimitHenselianPair | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FiniteGabberPolynomial | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FiniteGabberPolynomialRelation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FiniteLocalHenselian | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.FiniteOverHenselianLocalProduct | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.GabberIntegralSectionFactor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianApproximationAlgHom | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianEtaleRetraction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianEtaleRetractionExistence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianFactorizationCriterion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianFiniteEtaleEquivalence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianIntegralIdempotentLifting | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianLocalRootLifting | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianOfEtaleSectionLifting | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianPairApproximation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselianPairPrimeConnected | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselizationColimit | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselizationPairGRing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselizationPairGRingCore | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselizationStageMap | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.HenselizationUniversalProperty | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.IntegralOverHenselianPair | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.LiftIdempotentUpstairs | not queried; no edit | Private direct importer; compiled against revised module; unchanged. |
| Sheaf.RingTheory.MapIntoHenselianColimit | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PairHenselization | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PairHenselizationColimit | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PairHenselizationCompletionFaithfullyFlat | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PairHenselizationFlatQuotients | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PairHenselizationNoetherianCompletion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PopescuEnlargeSolutionModulo | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PopescuResolveCharP | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PopescuSmoothing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PopescuSolutionModulo | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.PopescuSolutionModuloChoose | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.SmoothPolynomialFactorization | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.StrictHenselizationCompletionFlat | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.StrictHenselizationCompletionNoetherian | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.StrictHenselizationNoetherian | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.StrictHenselizationRegular | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| Sheaf.RingTheory.StrictlyHenselianQuotient | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| TargetsCheck | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.AffineSpace | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Defs | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Inversion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Perverse | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Properties | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.FourierTransform.Properties.Stalk | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Gabber | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Integral.BaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.Integral.Exact | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not queried; no edit | Beyond the private direct import; no declaration or public interface changes. |

## Status

landed 20261012T112832-L-764975 2026-10-12 (merge of deliver/C1/Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial)
