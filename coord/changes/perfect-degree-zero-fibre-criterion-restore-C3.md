# AlgebraicGeometry.perfect_degreeZero_fibre_criterion

## Reason

Restore the module under its `coord/rework.tsv` assignment, preserving the archived
proof and Lean attachment. Its old public derived-pullback import is now an empty
withdrawn module. The current declaration `AlgebraicGeometry.derivedPullback` belongs
to the adopted source module. Import it publicly so that the theorem's public
signature elaborates. The original archive fails with unknown identifier
`derivedPullback` at its public signature; the replacement compiles cleanly.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

No declaration signature, proof body, definition, or visibility changes.
The removed wrapper currently contains no declarations or imports, so removing it
loses no current public interface. The replacement exposes the canonical existing
`derivedPullback` used by the unchanged theorem and its dependencies.

## Users

No present Lean module imports the quarantined item. A search of the current
library and quarantine finds the following archived direct consumer; it remains
preserved and is not part of this delivery. Its theorem proof is still `sorry`,
and it imports the item for the planned degree-zero criterion.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | C3 | Restore complete proof; replace withdrawn public import. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed; quarantined | Unchanged theorem interface; no consumer adaptation needed. |

The DAG attachment, all dependency edges and the unit route are preserved. No
statement or definition used by a target is changed, so no target statement
review is reopened.

## Status

landed 20261021T004818-L-1790357 2026-10-21 (merge of deliver/C3/Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion)
