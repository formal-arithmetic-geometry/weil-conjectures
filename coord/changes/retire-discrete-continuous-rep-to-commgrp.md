# Rep.discreteContinuousRepToCommGrp

## Reason

Retire the duplicate requested by `coord/retire-items.tsv` and the human's
2026-10-20 retirement decision. The item has zero `sorry` holes. The official
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrp` already contains
all eight public declarations with identical signatures and construction/proof
bodies. Its only mathematical import difference is that it imports
`WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction` and locally enables
its forgetful instances, instead of importing
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets`
and thereby exporting two global forgetful instances.

The current source includes A9's `212359aa7b` import migration, which overlapped
the earlier returned delivery. Rechecked the retirement against that version:
the whole construction from `variable (G : Type u)` through `end Rep` remains
byte-identical to the official twin. The earlier base `d92f73d8e` is superseded;
this packet retires the current duplicate and preserves A9's upstream G-set
interface in the unchanged equivalence assembly.

The two direct consumers import the official twin and enable its two local
forgetful instances. Their existing declarations, signatures, visibility, and
proof bodies remain verbatim. The DAG definition points to the retained upstream
construction. No source-library file or target statement changes. The represented
pointwise-addition construction and the blueprint unit route are preserved.

## Old

The duplicate module defined `Rep.discreteContinuousRepToAction`,
`Rep.discreteRepEquivariantFunctions`, `Rep.discreteRepEquivariantPresheaf`,
`Rep.discreteRepEquivariantRepresentable`, `Rep.discreteRepCommGrpObject`,
`Rep.discreteRepCommGrpMap`, `Rep.discreteContinuousRepToCommGrp`, and
`Rep.discreteContinuousRepToCommGrp_faithful`.

Its main signature was:

```lean
noncomputable def discreteContinuousRepToCommGrp :
    DiscreteContinuousRep.{0, u, w} ℤ G ⥤ CommGrp (DiscreteContAction (Type w) G)
```

In both direct consumers:

```lean
public import Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp
```

## New

Withdraw `lean/Sheaf/CategoryTheory/DiscreteContinuousRepToCommGrp.lean` through
`deleted.txt`; the delivery tool retains an empty historical module. All eight
names above, with the identical signatures and bodies, now come from the official
twin. Both direct consumers use:

```lean
public import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrp
```

Inside each consumer's existing `namespace Rep`:

```lean
attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂
```

The local attributes supply the same discrete-topology forgetful functors as the
old global instances; they do not export a new instance or declaration. The node
`def-exc-discrete-continuous-rep-to-commgrp` keeps its mathematical statement and
points its Lean attachment to the official twin.

## Users

The table includes all downstream modules reported by `tools/downstream.py`.
All 36 current downstream import closures were checked: the change introduces no paired
`Sheaf.X`/`WeilConjectures.X` modules and leaves no import of the withdrawn module.
The two direct consumers and the unchanged equivalence assembly plus its immediate
consumer compile against the changed imports. The latter two publicly import
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets` themselves, preserving the global
forgetful instances used in the remaining downstream statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp | unclaimed | Unchanged source compiled against adapted dependencies; same statement and proof. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux | unclaimed | Unchanged source compiled against adapted dependencies; same statement and proof. |
| Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj | unclaimed | Repoint public import to official twin; enable its two local forgetful instances; compiles. |
| Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull | unclaimed | Repoint public import to official twin; enable its two local forgetful instances; compiles. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No source edit; sees same public construction through unchanged equivalence interface. |

## Status

landed 20261020T154048-L-3036551 2026-10-20 (merge of deliver/K9/Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp)
