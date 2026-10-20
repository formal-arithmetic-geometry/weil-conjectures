# Rep.discreteContinuousRepToCommGrp_full

## Reason

Complete the retirement listed in `coord/retire-items.tsv`. The Sheaf module is an
already proved duplicate with zero holes. Its retained official upstream twin is
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull`.
After the prerequisite construction retirement, both files publicly import the
same upstream construction. Their entire contents from `universe u w` through
`end Rep` are byte-identical, including the private helper, local instance
attributes, theorem signature and proof. Thus the earlier SUPERSET dependency
obstacle in the retirement table no longer applies.

The sole direct importer is unclaimed. Change only its private proof import.
Retain every DAG dependency and attach the fullness node to the upstream module;
the parent still uses the identical theorem. No source-library file, target,
definition, mathematical statement or unit route changes.

## Old

In `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull`:

```lean
theorem discreteContinuousRepToCommGrp_full
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    (discreteContinuousRepToCommGrp (G := G)).Full
```

In `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux`:

```lean
import Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull
```

## New

The identical theorem signature above, and its complete existing proof, come from
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull`. Withdraw the
Sheaf copy via `deleted.txt`, which the delivery tool turns into an empty historic
module. The sole consumer uses:

```lean
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull
```

The node `lem-exc-discrete-continuous-rep-to-commgrp-full` changes only its Lean
attachment to that retained upstream theorem. Its statement, proof, proof_deps,
and every parent dependency are preserved.

## Users

All current downstream source import closures were inspected. No newly introduced
Sheaf/upstream twin pair was found. The migrated direct consumer and its unchanged
immediate consumer `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp` compile.
The upstream fullness module was compiled independently, and `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux | unclaimed | Migrate the proof import to the identical upstream theorem. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No source edit; the same fullness theorem remains available through the equivalence assembly. |

## Status

landed 20261020T161732-L-3529222 2026-10-20 (merge of deliver/E1/Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull)
