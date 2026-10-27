## What changed

Proved `AlgebraicGeometry.groupoid_source_pullback_translation` without changing its
statement or any public import. The forward and inverse morphisms are explicit pullback
lifts. A proved private cancellation helper combines associativity and the right unit law;
the inverse laws follow by pullback extensionality. The translation makes the composition
square cartesian. Fibre-degree base change on the two cartesian squares proves invariance,
and the existing proved fibre-dimension local-constancy theorem supplies the open strata.
Added its module as a private proof import and updated the item node to this proof route.
No other existing module or node was changed.

Validation: the item compiled cleanly through `lcompile.py` in 3.6 seconds.
The theorem signature and public imports are unchanged; all Lean lines are at most
100 characters. The dependency import is acyclic.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.groupoid_source_pullback_translation`
(node `lem-a1-groupoid-source-pullback-translation`).
The private helper `AlgebraicGeometry.groupoid_comp_cancel` is also proved.
Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.

## No longer needed

Removed the explicit private import `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`;
the public `FiberDegree` import already exposes it. No original public import was removed.
The direct dependency on `lem-weil-pbc-finite-flat-rank-iso` is replaced by the existing
proved `lem-weil-pbc-finite-locally-free-degree-locally-constant`, which uses that rank
lemma internally. Fibre-degree base change is already proved in the public `FiberDegree`
module. No dependency module is withdrawn or claimed globally unnecessary. No unit route
is bypassed, and no new statement modules are introduced.

## Where the brief, the DAG or earlier work was wrong

The planned argument is sound, including the empty-scheme and rank-zero cases.
The rank/fibre comparison needed by the plan is already packaged in the existing proved
local-constancy theorem, and fibre-degree base change avoids doing that comparison twice.
Library and Mathlib searches (LeanFinder, Loogle and grep) found no existing internal
scheme-groupoid translation theorem; the proof uses the supplied groupoid axioms directly.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
