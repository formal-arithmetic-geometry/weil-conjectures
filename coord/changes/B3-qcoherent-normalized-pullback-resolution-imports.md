# qcoherentNormalizedComparison_pullback_square: resolution-import repair

## Reason

This is the listed rework assignment from coord/rework.tsv, upstream synchronization
5f7b33eac. The archived item fails on import because both the retired Sheaf resolution
implementation and the adopted WeilConjectures implementation declare
AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv.
The dispatcher marks this assignment as repair. Restore the archived item, retaining its
statement, complete source proof plan, existing hole, node and dependencies.

CoherentEtaleComparisonMorphismExists and CoherentEtaleEffacingSequence are unclaimed.
They also import the duplicate implementation and must use the adopted extension so
that CanonicalCoherentEtaleComparison can coexist with the adopted normalization API.
CanonicalCoherentEtaleComparison has meanwhile been synchronized in the shared checkout;
its current source is retained without any edit, including all its new public caches.
No definition or mathematical statement changes. No adopted source file changes.

## Old

In CoherentEtaleComparisonMorphismExists, CoherentEtaleEffacingSequence and the archived
QcoherentNormalizedPullbackSquare:

```lean
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

The item also had the following proof-only import, although its statement uses
moduleCohomologyFMap:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

## New

In all three modules:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
```

In the item, before proof imports:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

The naturality node's Lean attachment now names the adopted module that declares the
same theorem. Its declaration list contains the declarations actually defined in that
module; the attachment note locates the cache helpers in the adopted extension.
The mathematical statement, proof steps and dependencies of the node are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | B3 | Restored from quarantine; duplicate import removed; statement dependency made public; compiled. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists | unclaimed | Only its obsolete proof import changes; compiled. |
| Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence | unclaimed | Only its obsolete proof import changes; compiled. |
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | Sole direct importer of both support modules; current source compiled unchanged against their replacements. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Quarantined direct parent; its dependency and the item's full signature are preserved. Its separate rework is not included. |

Both support imports are private. Their public signatures and definition bodies are
identical, so their consumer's meaning does not change. The restored item has precisely
the archived theorem signature. Its new public import exposes the existing declaration
already used there. There is no target-meaning change requiring a definition review.

## Status

landed 20261020T154037-L-3031943 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare)
