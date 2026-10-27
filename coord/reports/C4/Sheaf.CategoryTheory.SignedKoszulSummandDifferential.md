## What changed

Proved `CategoryTheory.ringedNegativeKoszulSummand_D₂_succ` from the generic
second total differential formulas, the ordered basis differential theorem, and
a one-index scalar/equality transport lemma. Added the proof-only import of the
transport module. The ordered basis differential theorem remains unchanged.

## Proved and sorry left

Closed the sorry in `ringedNegativeKoszulSummand_D₂_succ`.
The existing sorry in `ringedNegativeKoszulBasis_d_succ` remains.
Added `ringedNegativeKoszulSummand_D₂_term` as a strictly smaller split-off
statement; its proof is still sorry for a future worker.

## No longer needed

None. The proof uses all imports and dependencies retained by the module.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

Added `lem-cbc-signed-koszul-summand-term-transport` for the scalar-action and
equality-transport calculation for one erased-index summand. It is strictly
smaller than the finite-sum differential theorem and is imported by the proof.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
