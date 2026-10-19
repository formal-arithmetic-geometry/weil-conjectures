## What changed

Proved `AlgebraicGeometry.Scheme.finite_stage_karoubian` in
`Sheaf.Paper.PbcFiniteStageKaroubian`, with its signature and imports unchanged.
Extracted the rational t-structure and `tE.bounded = ⊤` from
`pbc_localized_tstructure T l E`, converted boundedness to the objectwise hypothesis,
and applied `isIdempotentComplete_of_bounded` and
`isEquivalence_toKaroubi_and_isTriangulated_of_bounded` to that same t-structure.
This implements all three existing DAG steps and preserves the unit route.
No definition, statement, node, or consumer needed adaptation.

Read the source theorem, its node, the sk-rem-rest unit, and all declared
dependency statements. The launcher searches for bounded-t Karoubianity returned
eight general triangulated-category results from Lean Finder and no matches from
Loogle or the Mathlib grep. The existing source-library theorems already give the
short specialization needed here. Remote single-file compilation passed cleanly
in 3.1 seconds after removing an unnecessary local instance.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finite_stage_karoubian`
(node `thm-weil-pbc-finite-stage-karoubian`).
Holes closed: 1 of 1. Holes added: 0. Split off: 0.
No `sorry` remains in the delivered module. The proof uses the existing library
dependencies; their remaining obligations are unchanged.

## No longer needed

None. No imports, modules, or nodes were pruned. Both declared proof theorems
are used, and the raw rational-category and Karoubi constructions remain in
the statement. The Tor-dependent final clause of `pbc_localized_tstructure`
is unused, as the existing DAG explicitly intends; it introduces no hypothesis.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface fault found. The existing proof plan fits the
available declarations without changes. One remote compilation request reported
no server answer within 201 seconds; its retry compiled in 3.1 seconds.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
