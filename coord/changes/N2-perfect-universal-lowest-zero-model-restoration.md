# AlgebraicGeometry.Scheme.perfectUniversalLowest_zero_model

## Reason

Restore the module preserved in quarantine by the rework assignment. The archived
source fails to compile because its two Sheaf derived-pullback compatibility
modules have been withdrawn. The statement needs the adopted public declaration
`AlgebraicGeometry.derivedPullback`; its proof needs the adopted composition theorem.
The first compile reported unknown identifiers for these two declarations.

## Old

The archived module imports:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

The complete theorem signature and proof body are preserved verbatim. Its local
model is obtained from the same five declared proof dependencies. The node keeps
its Lean attachment, statement, proof steps and dependencies; only its proof-origin
note records this restoration. No definition or target statement changes, so no
target statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | N2 | Restored and compiled without holes. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback | No local claim record; quarantined | Same theorem signature and application; no adaptation. |

`tools/downstream.py` reports the item as unknown while it is quarantined. Direct
searches of `lean/` and `quarantine/` find just the parent above. Its application
passes the same arguments and uses the same model conclusion. The corresponding
parent node still lists this item in its proof dependencies and proof step uses.
The parent also has independent withdrawn imports and a quarantined dependency;
its separate restoration is outside this packet. No consumer file is changed.

## Status

landed 20261020T221259-L-4168390 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel)
