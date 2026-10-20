## What changed

Reattached `lem-sc-rectangle-ordinary-geometric-pullback` to the existing proved
`AlgebraicGeometry.rectangle_ordinary_geometric_pullback` in
`WeilConjectures.AlgebraicGeometry.RectangleOrdinaryGeometricPullback` and withdrew
the duplicate Sheaf module via `deleted.txt`. The source theorem has exactly the
current Sheaf signature and the node's recorded signature. The source proof
already carries out all three existing DAG steps; its mathematical dependencies
and the unit route are retained.

The only direct DAG parent,
`lem-sc-rectangle-ordinary-geometric-comparisons`, is already attached to the source
module that imports this upstream theorem and calls it at line 96. Its dependency
still names the same node and requires no source or node adaptation. Scans of all
live and quarantined Lean sources found no remaining import of the Sheaf copy.
No quarantine file or adopted-source file was changed.

Validation: all three required `msearch.py` searches completed. Local source
comparison found identical signatures. `lcompile.py` compiled an import of the
upstream module and a check applying the upstream theorem to the entire unchanged
Sheaf statement. The imported theorem's axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`.

Change record:
`coord/changes/C3-rectangle-ordinary-geometric-pullback-source-reuse.md`.

## Proved and sorry left

This is a duplicate-module rework repair. The current Sheaf module and its
quarantined predecessor have zero proof holes. Holes closed in this delivery: 0.
Holes added: 0. Split-off statements: 0. No `sorry` remains or is added.

The existing complete proof of
`AlgebraicGeometry.rectangle_ordinary_geometric_pullback` is preserved in the
adopted source module and is now the node's sole Lean attachment. No proof is
claimed as newly written.

## No longer needed

The duplicate module
`Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback` is withdrawn.
Its public import of
`WeilConjectures.AlgebraicGeometry.QCohInverseBaseChangeMate` and proof imports of
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition` and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting` disappear with that copy.
Those modules remain needed by the retained upstream proof and are not pruned
from the mathematics. The archived Sheaf composition import is not restored.

No DAG node or mathematical dependency is removed: the item node is retained and
reattached, and its sole parent's dependency is unchanged. The upstream proof is
an exact replacement for this node, not a bypass of an unfinished parent or unit.

## Where the brief, the DAG or earlier work was wrong

The rework row describes the pre-sync archived import error. B5 subsequently
restored a complete proof, so the current module is already sorry-free. However,
the exact theorem also exists in the adopted source library. Repeating the proof
would retain duplicate public declarations; reuse of that proved theorem repairs
the remaining overlap and makes the stale Sheaf attachment unnecessary.

The old DAG attachment still pointed to the duplicate Sheaf copy while its parent
already imported the upstream copy. This delivery reconciles that attachment with
the actual parent proof and preserves all existing proof dependencies.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
