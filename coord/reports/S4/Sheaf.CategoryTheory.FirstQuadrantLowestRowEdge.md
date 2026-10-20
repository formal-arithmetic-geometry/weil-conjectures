## What changed

Proved `CategoryTheory.first_quadrant_lowest_row_edge` in
`Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge`, without changing its signature or
visibility. Vanishing propagates by homology; zero incoming and outgoing differentials
give the canonical cycle and homology isomorphisms. Their recursive composites construct
all the required survival maps and compatibility identities. Vanishing graded pieces
force consecutive filtration steps to agree, and finite reverse induction gives
`(F m).F 1 = ⊥`, including the case `m = 0`. The explicit edge composite satisfies the
specified quotient square and is an isomorphism.

Updated the existing node `lem-pur-first-quadrant-lowest-row-edge` in its proof fields to
record this implementation. Removed the unused private import
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`. No new modules, declarations,
statement changes, definition changes, consumer adaptations, or change records.

Validation: searched with LeanFinder, Loogle and grep via msearch, and read the related
proved `SpectralSequence.nonempty_abutment_iso_row_zero` source argument. Read the
recorded dependency signatures and Stacks Homology definitions of spectral sequences,
stable terms and filtrations. The proof follows all five existing DAG steps; the unit
route is unchanged. Every compile used lcompile.py on the single sandbox module.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.first_quadrant_lowest_row_edge`
(node `lem-pur-first-quadrant-lowest-row-edge`). Added 0 holes. There are 0 sorries left
in the item and no split-off statements. The proof uses Mathlib and the existing real
filtration definitions, with no admitted project theorem.

## No longer needed

Removed import `WeilConjectures.CategoryTheory.ExactCoupleConvergence`.
The proof no longer needs the exact-couple convergence declarations recorded on
`def-sp-convergence`: the theorem already assumes its convergence comparisons into
page `m + 2`, and explicitly describes survival by cycle inclusion and homology
projection. Removed `def-sp-convergence` from `proof_deps` and the proof steps that
formerly named it. Its statement dependency remains, since it explains the intended
stable-term convention. No claim is made that this module or node is globally
unreachable; it is pruned from this proof branch. No other imports or nodes are removed.
The row-zero theorem was read as a proof template and is not imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or disputed statement was found. The original private
exact-couple convergence import was unnecessary for the general page-based statement.
The existing five-step argument suffices without new intermediate results.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
