## What changed

Filled `AlgebraicGeometry.ProEtale.adicComplexTowerEvaluation_inverts` in
`Sheaf.Paper.SequentialDerivedInverseLimit`. Mathlib's
`HomologicalComplex.quasiIso_iff_evaluation` sends a tower quasi-isomorphism to a
quasi-isomorphism at each index. `DerivedCategory.Q` inverts each evaluated map;
`NatTrans.isIso_iff_isIso_app` then proves invertibility of the entire natural
transformation. Its components are definitionally the evaluated maps, so all tower
transitions are retained. The proof applies to every complex and every index,
without boundedness, finiteness, or surjectivity assumptions.

The module compiles cleanly through `lcompile.py`. No declaration signature,
definition, visibility, or import changed. The proof follows the declaration's
existing source and natural-language proof (blueprint
`def-weil-pbc-derived-inverse-limit`, Stacks 05RU).

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.adicComplexTowerEvaluation_inverts`.
No holes remain in the item; no holes were added or split off.

## No longer needed

None. No proof-only imports were present or added. Existing public imports remain
part of the module's published interface. No new dependency node or module is
needed: Mathlib already proves the levelwise quasi-isomorphism criterion, and
localization and componentwise invertibility supply the rest.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The docstring correctly identifies
`def-weil-pbc-derived-inverse-limit`; its current DAG Lean attachment names the
separate `CompletedDerivedInverseLimit` module rather than this auxiliary
sequential-evaluation module. This delivery does not overwrite that attachment.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
