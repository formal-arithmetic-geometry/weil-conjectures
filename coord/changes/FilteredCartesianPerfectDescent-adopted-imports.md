# AlgebraicGeometry.filtered_cartesian_perfect_descent

## Reason

Restore the zero-hole module preserved at
`quarantine/Sheaf/AlgebraicGeometry/FilteredCartesianPerfectDescent.lean` by its
`coord/rework.tsv` assignment. The archived module imports the withdrawn empty
Sheaf modules for derived pullback and derived pullback composition. The current
DAG attaches those notions to the adopted WeilConjectures source modules.
Compiling the unmodified archive reproduces both failures (3.0 seconds):

```text
FilteredCartesianPerfectDescent.lean:82:21: error(lean.unknownIdentifier):
Unknown identifier `derivedPullback`
Note: A public declaration `derivedPullback` exists but is imported privately;
consider adding `public import WeilConjectures.AlgebraicGeometry.DerivedPullback`.
FilteredCartesianPerfectDescent.lean:162:46: error(lean.unknownIdentifier):
Unknown identifier `exists_derivedPullbackComposition`
```

Restore those imports so the unchanged statement publicly sees `derivedPullback`
and the unchanged proof can use `exists_derivedPullbackComposition`.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

Every other byte of the archived Lean module is preserved. No declaration,
definition, theorem signature, target statement or target meaning changes.
The existing node attachment and all four proof dependencies remain valid.
The repaired file compiles through `lcompile.py` in 9.3 seconds without warnings.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent --allow-missing
--uses AlgebraicGeometry.filtered_cartesian_perfect_descent` finds zero live
library importers, since the assigned module is quarantined. Searching both
Lean roots and `quarantine/` additionally finds the parent below, whose DAG node
still explicitly depends on this theorem. Its call uses exactly the preserved
signature. Current claim records assign this item to J1.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | J1 | Restore the archive with the adopted statement and proof imports. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed in current snapshot; quarantined | Unchanged theorem call; no adaptation required. |

The quarantined parent independently has stale imports. This restoration does
not alter that parent or remove any dependency. No forced adaptations.

## Status

landed 20261025T041219-L-1094134 2026-10-25 (merge of deliver/J1/Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent)
