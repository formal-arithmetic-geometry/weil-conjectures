# AlgebraicGeometry.perfect_local_models_stage_comparisons

## Reason

Restore the stage-comparison module quarantined by the cluster-restore global
build failure (coord/rework.tsv). The archived source publicly imports the
withdrawn Sheaf derived-pullback module, so its public theorem cannot resolve
`derivedPullback`. It also registers cached abelian structures without a visible
import of their defining module. The repair imports the current source-library
pullback publicly and the cache module privately. No mathematical construction
or theorem signature is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The following local registration had no visible import of its declarations:

```lean
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel
```

The local registration uses the same existing canonical abelian abbreviations,
plus the existing exact-restriction instances, with local priority 2000. Add:

```lean
attribute [local irreducible] Scheme.Opens.toScheme
```

Both the gluing helper and the main theorem use
`backward.isDefEq.respectTransparency true` and
`backward.isDefEq.respectTransparency.types true` locally. This prevents repeated
expansion of the construction of open subschemes during type comparison. The
main proof passes its shared derived-category instances explicitly to the
transition theorem and the gluing helper, binds each application before
unpacking it, and keeps the stage geometry as named let bindings. This repairs
elaboration, not mathematical definitions. Heartbeat budgets are reduced from
800000/400000 to 160000/80000. The 60-second file limit is unchanged.

The theorem signature and all four mathematical proof dependencies are preserved.
All attributes are local to this module; no imported declaration is edited.

## Users

The module is absent from the active library, so `tools/downstream.py` reports
`unknown module`. A full text search of lean/ and quarantine/ finds just the
following consumer besides the archived item itself. DAG references retain the
parent and the item's existing Lean attachment. No withdrawal is proposed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | B2 | Restore and repair imports and proof elaboration. |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | quarantined | Same theorem name, binders, universes and conclusion; no adaptation. |

No target statement or definition is changed, so semantic review is not reopened.

## Status

landed 20261023T104701-L-3413361 2026-10-23 (merge of deliver/B2/Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons)
