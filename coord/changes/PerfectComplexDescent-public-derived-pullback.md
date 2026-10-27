# AlgebraicGeometry.perfect_complex_descends

## Reason

Restore the zero-hole module preserved at
`quarantine/Sheaf/AlgebraicGeometry/PerfectComplexDescent.lean` by the rework row
for `Sheaf.AlgebraicGeometry.PerfectComplexDescent`. The original row records a
cluster rollback. The newest build diagnostic, from `a7d709d57a` on 2026-10-24,
identifies the archived public DerivedPullback import, which now names a withdrawn
empty module. Compiling the archive reproduces:

```text
PerfectComplexDescent.lean:68:17: error(lean.unknownIdentifier):
Unknown identifier `derivedPullback`
Note: A public declaration `derivedPullback` exists but is imported privately;
consider adding `public import WeilConjectures.AlgebraicGeometry.DerivedPullback`.
```

The actual derived pullback is the adopted source declaration. Its module must
be public because the theorem's public statement uses it. This repair restores
that statement dependency instead of relying on private proof imports.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

Every other byte of the restored Lean file is unchanged from the quarantine
archive: theorem signature, docstrings and proof all remain intact. No definition,
target statement or target meaning changes. The existing node attachment and its
three proof dependencies are preserved. No DAG change is required.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.PerfectComplexDescent
--allow-missing --uses AlgebraicGeometry.perfect_complex_descends` reports zero
current library importers because the item is quarantined. Searching both live
Lean roots and `quarantine/` additionally finds the archived parent below. Its
node still explicitly uses `lem-pc-perfect-complex-descent`, which this delivery
restores. The current claim record names J4 for the item; the archived parent
has no claim in the current snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | J4 (assigned) | Restore the archive with the public import required by its unchanged signature. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed in local snapshot; quarantined | Calls the same theorem with the same arguments; no adaptation. |

The archived parent independently has stale Sheaf imports; this restoration does
not modify it or withdraw its still-needed dependency. There are no forced
adaptations in this packet.

## Status

landed 20261025T013923-L-4038690 2026-10-25 (merge of deliver/J4/Sheaf.AlgebraicGeometry.PerfectComplexDescent)
