# WeilConjectures.finiteHomDomain_transpose

## Reason

Keep the same four clauses behind the concrete proposition
`FiniteHomDomainTransposeLaws`. Direct specialization of the expanded naturality
clause makes the kernel repeatedly compare the definitionally equal ring instances
`ULift.commRing.toRing` and `ULift.ring` inside the derived categories. An isolated
proof at the original expanded type times out in the kernel; the same proof at the
named predicate checks in milliseconds (6.6 seconds including imports).

This is a presentation change, with no mathematical change. The predicate is the
literal four-clause conjunction at abstract closed categories, functor and tensor
comparison, using `coefficientBaseChangeHom`. At the given finite coefficient data
this is definitionally the original conjunction: `etaleFiniteHomCanonical` is the
abbreviation for exactly this `coefficientBaseChangeHom` application. All objects,
universes, hypotheses, equations, uniqueness assertions and the canonical map are
preserved. No data construction or target declaration is changed.

## Old

```lean
theorem finiteHomDomain_transpose {n m : ℕ} (h : m ≤ n) :
    (∀ (U K M : finiteHomEtale l E X n)
      (t : (finiteHomEtaleClosed l E X n).tensor.obj (U, K) ⟶ M),
      ∃! g : U ⟶ (finiteHomEtaleInternalHom l E X n).obj (op K, M),
        (finiteHomEtaleClosed l E X n).tensor.map (Prod.mkHom g (𝟙 K)) ≫
          (finiteHomEtaleClosed l E X n).evaluation K M = t) ∧
    (∀ (U K M : finiteHomEtale l E X m)
      (t : (finiteHomEtaleClosed l E X m).tensor.obj (U, K) ⟶ M),
      ∃! g : U ⟶ (finiteHomEtaleInternalHom l E X m).obj (op K, M),
        (finiteHomEtaleClosed l E X m).tensor.map (Prod.mkHom g (𝟙 K)) ≫
          (finiteHomEtaleClosed l E X m).evaluation K M = t) ∧
    (∀ (K M : finiteHomEtale l E X n)
      (v : (finiteHomEtaleReduction l E X h).obj
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ⟶
        (finiteHomEtaleInternalHom l E X m).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)),
      (finiteHomEtaleClosed l E X m).tensor.map
          (Prod.mkHom v (𝟙 ((finiteHomEtaleReduction l E X h).obj K))) ≫
          (finiteHomEtaleClosed l E X m).evaluation
            ((finiteHomEtaleReduction l E X h).obj K)
            ((finiteHomEtaleReduction l E X h).obj M) =
        (finiteHomEtaleTensor l E X h).inv.app
            ((finiteHomEtaleInternalHom l E X n).obj (op K, M), K) ≫
          (finiteHomEtaleReduction l E X h).map
            ((finiteHomEtaleClosed l E X n).evaluation K M) ↔
      v = etaleFiniteHomCanonical l E X h K M) ∧
    (∀ (K K' M M' : finiteHomEtale l E X n) (f : K' ⟶ K) (g : M ⟶ M'),
      (finiteHomEtaleReduction l E X h).map
          ((finiteHomEtaleInternalHom l E X n).map (Prod.mkHom f.op g)) ≫
          etaleFiniteHomCanonical l E X h K' M' =
        etaleFiniteHomCanonical l E X h K M ≫
          (finiteHomEtaleInternalHom l E X m).map
            (Prod.mkHom ((finiteHomEtaleReduction l E X h).map f).op
              ((finiteHomEtaleReduction l E X h).map g)))
```

## New

```lean
theorem finiteHomDomain_transpose {n m : ℕ} (h : m ≤ n) :
    FiniteHomDomainTransposeLaws
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)
```

The new public definition `WeilConjectures.FiniteHomDomainTransposeLaws` is in the
same module and attached to the same DAG node. It has a concrete, hole-free body.
Its four clauses are proved by nine private categorical lemmas in this delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteHomDomainCalculus | E4 | Uses the named predicate; other existing signatures and definitions are preserved. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y2 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K3 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | T2 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Direct importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Transitive importer; no reference to the changed theorem; no adaptation. |

No downstream declaration refers to this theorem by name. The 98 transitive importers were searched for uses. The direct importer is
compiled unchanged against this delivery (successful batch compilation), as
recorded in the report; a whole-library build
remains the maintainer's check. None of
the five target signatures or definitions used by those signatures is changed.

## Status

landed 20261026T023105-L-519178 2026-10-26 (merge of deliver/E4/Sheaf.Paper.FiniteHomDomainCalculus)
