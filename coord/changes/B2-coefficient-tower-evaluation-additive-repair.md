# AlgebraicGeometry.ProEtale.SpTowerCalculus.levelComparison

## Reason

Restore the complete quarantined interface module and repair its assigned global-build
failure, confirmed against the current server queue and build-error records. The failing
line tries to infer evaluation additivity through preservation of binary products. Its
instance search fails to construct the required evaluation-additivity instance.

Instead use the already specified ordinary evaluation isomorphism. Its source is the
composite of the additive realization functor with the additive sequence-site evaluation.
Mathlib's `Functor.additive_of_iso` transfers this property to coefficient evaluation.
The subsequent exact-derived comparison is the original construction.

## Old

Inside the unchanged `levelComparison` definition:

```lean
  letI : (spCoefficientEvaluation l E T (q.abelian T).equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
```

The complete archived module is preserved at
`quarantine/Sheaf/Paper/CoefficientTowerShriekInterfaces.lean`; it is restored to its
original `lean/` path, with only the preceding proof term changed.

## New

```lean
  letI : (spCoefficientEvaluation l E T (q.abelian T).equivalence n).Additive :=
    Functor.additive_of_iso (q.ordinaryEvaluation T n)
```

This changes a proposition-valued instance proof, not the evaluation functor or its
normalization. All declaration signatures, structure fields, imports, visibility and
attributes are those of the archive. No new declaration, axiom or proof hole is added.
The DAG attachment `def-sp-coefficient-tower-shriek-interfaces` and all its dependencies
remain unchanged. The target statements and the meanings of their definitions are
unchanged; no statement re-review is needed for this proof-term repair.

## Users

The table lists the item and all transitive consumers reported by
`tools/downstream.py Sheaf.Paper.CoefficientTowerShriekInterfaces --allow-missing`.
The current direct importers are SectionCoordinates, GeometricComposition,
TransitionCompatibility, ShriekCalculus, TowerIntrinsicShriekTransition,
SmoothPurityTowerBinaryCounitPredicates and FieldShriekSystemModels. The latter
was restored concurrently while validation sources were being collected. Their current
sources compiled unchanged against the repaired item, each within 60 seconds;
the longest consumer took 54.5 seconds. Copies were then removed from the sandbox; no consumer source is delivered merely for validation. Quarantined consumers
retain their original interface and are not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | G3 | Restore full archive; repair local additive proof. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FiniteP1KummerBoundaryTransport | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FiniteP1KummerChernRealization | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.FiniteP1KummerComparisonIso | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TensorWordComparison | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TwistedPullbackCofinalModels | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TwistedPullbackLineMembership | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Same public signatures and constructions; no adaptation. |
| Sheaf.Paper.TwistedPullbackTateReduction | unclaimed | Same public signatures and constructions; no adaptation. |

## Status

landed 20261027T194421-L-818555 2026-10-27 (merge of deliver/B2/Sheaf.Paper.CoefficientTowerShriekInterfaces)
