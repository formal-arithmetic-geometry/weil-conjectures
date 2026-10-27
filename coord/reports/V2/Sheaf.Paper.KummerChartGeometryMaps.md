## What changed

In `Sheaf.Paper.KummerChartGeometryMaps`, completed the two existing projection
identities directly with Mathlib's `CategoryTheory.Limits.pullback.lift_fst`
(in the reverse direction) and `CategoryTheory.Limits.pullback.lift_snd`.
The definition of `TameRootExtensionChart.toPuncturedBase` is already the
pullback lift of precisely these two maps. This is the argument in the existing
docstrings, with no change to statements, definitions, imports, or the proof route.

The complete module compiled without warnings through `lcompile.py` in 3.3 seconds.
The delivery preflight independently checks compilation and declaration axioms.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.kummerChartOpen_commutes`.
- `AlgebraicGeometry.ProEtale.CondensedRing.kummerChartToOpen_commutes`.

Both belong to `def-sfb-kummer-chart-geometry-maps`. There are zero holes left
in the item module, zero holes added, and zero split-off statements.
The arguments work uniformly for empty component sets, empty opens, and every
natural-number parameter: they use only the universal pullback projection equations.

## No longer needed

None. No proof imports were added or removed. The existing public imports are
retained as the module's published reexports for its consumers; the two proofs
need only the already available chart definitions and Mathlib pullback equations.
The node has no planned proof dependencies to prune, and no other module is
withdrawn or made unnecessary by these proofs.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The historical rework row records quarantine after
a `ProjectiveLineGenusZero` dependency failure. The current item source is present,
and the unchanged public imports compile against the current server snapshot.
No quarantine archive is removed, and no definition or consumer repair is needed.
The existing docstring proofs are implemented verbatim; there is no route change
requiring a DAG update.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
