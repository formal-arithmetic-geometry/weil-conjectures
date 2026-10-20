# Rep.discreteContinuousRepToCommGrp_essSurj

## Reason

Retire the duplicate listed in `coord/retire-items.tsv`. Its prerequisite functor
has now migrated to the official upstream module (K9's landed retirement), so
this retirement no longer combines two copies of that prerequisite. The current
Sheaf and WeilConjectures theorem modules are identical after removing the
copyright header and normalizing whitespace: same imports, local instances,
universes, statement, and complete constructive proof.

There are zero holes in the item. The change removes a duplicate declaration
and preserves its proved upstream instance. No file of the adopted source tree
is edited. The parent node and the unit route continue to use the same theorem.

## Old

```lean
theorem discreteContinuousRepToCommGrp_essSurj
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    (discreteContinuousRepToCommGrp (G := G)).EssSurj
```

Declared by `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj`.
The sole direct consumer used this private proof import:

```lean
import Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj
```

## New

The identical signature and proof are retained in
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj`.
Withdraw the Sheaf copy via `deleted.txt`, and point the existing node's Lean
attachment to the retained theorem. Keep its mathematical statement, proof,
proof dependencies, and all parent dependencies unchanged. In the direct consumer:

```lean
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj
```

This imports the exact same theorem of the exact same functor. In particular,
non-Hausdorff groups, arbitrary carrier universes, and arbitrary chosen Cartesian
structures have the same hypotheses. No target statement or definition changes.

## Users

The following is the source import graph's full downstream closure (34 modules),
matching `tools/downstream.py`. The repaired auxiliary module compiled on the project server in 1.7 seconds
with no warnings. The earlier packet also compiled its unchanged immediate
consumer. Its only
textual user of the theorem is the direct consumer, which changes one import.
The public imports and instances of that consumer remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux | unclaimed | Replace the proof import by the upstream twin; theorem signature and proof unchanged. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No edit; identical theorem and declarations remain available through the equivalence assembly. |

## Returned-delivery repair

The accepted head `d539d3b29a` could not land because E1's later landing
`bc0643a7d0` changed the adjacent fullness import in the same auxiliary module.
Recreated the sandbox copy from the current `sheaf-dag` source, then changed
only the essential-surjectivity import shown above. In particular, the repaired
packet preserves the upstream fullness import already landed by E1. No source
library file, public import, signature, instance, or proof body is changed.
The repaired auxiliary module compiled on the project server without warnings.

## Status

landed 20261020T221119-L-4146337 2026-10-20 (merge of deliver/D4/Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj)
