## What changed

Filled the proof of `Submodule.projective_of_finite_of_projective_ideals` in
`Sheaf.RingTheory.SemihereditaryFiniteFreeSubmodule`. Added the proof-only import
`Mathlib.RingTheory.Finiteness.Basic` for finite generation of images and preservation
of finite generation by surjections. The statement and public imports are unchanged.

The proof implements all six steps of the node's rank induction. At successor rank,
it uses coordinate zero (the coordinate choice is immaterial), splits the projection
onto its image ideal using projectivity, and constructs the retraction
`q(x) = x - s(p(x))` onto the kernel. Surjectivity of this retraction proves the kernel
finite. Deleting coordinate zero embeds the kernel into the smaller finite free
module. Induction and the resulting linear equivalence give projectivity of the
kernel. Lifts from the kernel and the image ideal combine by the formula in the
existing proof plan to give the required lift from the original submodule.

## Proved and sorry left

Closed the one original hole in
`Submodule.projective_of_finite_of_projective_ideals`
(node `lem-sfb-semihereditary-finite-free-submodule`). No holes added or split off;
no `sorry` remains in the delivered module. The proof uses only proved Mathlib
results, with no project theorem left as an assumption beyond the stated hypotheses.
The zero-rank case follows from the free-module instance for a subsingleton module;
the induction also covers the zero ring and zero image ideal.
The completed module compiled cleanly through `lcompile.py` in 2.8 seconds;
its signature was checked byte-for-byte against the original, and all lines are
at most 100 characters.

## No longer needed

None. Both declared dependency nodes, `def-weil-pbc-projective-module` and
`def-weil-finitely-generated-module`, are used through their existing Mathlib
interfaces. No imports, modules, or DAG dependencies were removed. No unit route
was bypassed, and no new statement was needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The proof plan works unchanged up to choosing the
first coordinate instead of the last coordinate. The Mathlib search found no
existing theorem with this conclusion and ideal hypothesis. The required glue is
proved directly in the assigned module; no definition or consumer repairs were needed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
