## What changed

Replaced the sole proof hole in
`lean/Sheaf/AlgebraicGeometry/CompatibleCompactificationTriangle.lean`:
`AlgebraicGeometry.exists_compatible_compactification_triangle`.
All statements, definitions, docstrings, visibility and imports are unchanged.

The proof follows the five steps of
`lem-weil-pbc-compatible-compactification-triangle` (Stacks Tag 0F7J).
Properness supplies qcqs for the prescribed ambient scheme. Mathlib composition
instances supply separatedness and finite type for `f ≫ d.i`, and the existing
`NagataCompactification` constructs `e`. The monicity pullback square
`IsPullback (𝟙 X) f (f ≫ d.i) d.i` lets `Compactification.ofIsPullback`
construct the required compactification of `f` directly on `X`. Its two projection
lemmas give the equations. Quasi-compactness of its open immersion follows from
`Compactification.quasiCompact_openImmersion`; Mathlib base-change and composition
instances give the other geometric properties. The last factorization is the
composition of the two compactification equations.

LeanFinder, Loogle and grep were searched before writing the proof. The source
library's `Compactification.restrict` implements the same base-change argument;
the already imported `ofIsPullback` interface suffices without another import.
The single-file compile passed in 2.3 seconds; its one unnecessary-simpa warning
was removed before delivery verification.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_compatible_compactification_triangle`
(node `lem-weil-pbc-compatible-compactification-triangle`).
Added 0 holes, split off 0 statements. No `sorry` remains in the delivered module.
The delivery tool checks compilation and the theorem's axioms independently.

## No longer needed

None. Both proof imports (`WeilConjectures.Compactification.NagataCompactification`
and `WeilConjectures.Compactification.BaseChange`) are used. No import, node or
module is pruned, and no unit statement or proof step is bypassed. The existing
DAG plan remains applicable and is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface repair was needed. The plan's explicit identification
of the base-changed source with `X` is already packaged by Mathlib's
`IsPullback.of_horiz_isIso_mono` and the source library's
`Compactification.ofIsPullback`, so no new intermediate statement is needed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
