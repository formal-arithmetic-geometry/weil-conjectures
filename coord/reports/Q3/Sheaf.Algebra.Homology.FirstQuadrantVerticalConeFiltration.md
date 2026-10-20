## What changed

Restored the quarantined module
`lean/Sheaf/Algebra/Homology/FirstQuadrantVerticalConeFiltration.lean` and completed
`HomologicalComplex₂.firstQuadrant_vertical_cone_filtration` using its existing
constructive proof. The stale proof-only import of
`Sheaf.CategoryTheory.Filtration` was removed: the adopted upstream filtration API
already supplies the required declarations, and retaining that import causes the
recorded `IsExhaustive` name collision. All theorem statements, definitions, and
public imports are preserved.

Validation: the module compiles directly with `lcompile.py`, and the complete sandbox
import closure compiles with `lcompile.py --all`.

## Proved and sorry left

Closed the one archived hole:
`HomologicalComplex₂.firstQuadrant_vertical_cone_filtration`
(node `lem-sp-first-quadrant-vertical-cone-filtration`). Zero `sorry`s remain and no
new `sorry`s were added.

## No longer needed

The proof-only imports `Sheaf.CategoryTheory.Filtration` and
`Sheaf.CategoryTheory.DoubleComplexTotal` are no longer needed. The adopted upstream
filtration declarations are already available through the existing public imports,
and the proof uses the explicit cone-tail construction rather than the withdrawn
double-complex filtration declarations. No mathematical DAG dependency is pruned;
no modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined because its old proof-only import conflicted with the
adopted upstream `WeilConjectures.CategoryTheory.CanonicalFiltration` declarations.
Removing that stale import restores the module without changing its mathematics. The
DAG proof plan and theorem statement remain correct.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
