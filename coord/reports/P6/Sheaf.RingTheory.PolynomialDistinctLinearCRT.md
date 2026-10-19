## What changed

Replaced the sole `sorry` in
`Polynomial.quotient_prod_X_sub_C_algEquiv_pi` with the stated Chinese remainder proof.
The proof obtains pairwise coprime linear factors, identifies the intersection of their
principal ideals with the product ideal, composes the CRT ring equivalence with evaluation
on every factor, and upgrades the result to an algebra equivalence by checking constants.
Its representative formula is proved explicitly. The statement and imports are unchanged.
The proof works uniformly for `n = 0`, where the quotient and function space are trivial.

## Proved and sorry left

Closed one hole: `Polynomial.quotient_prod_X_sub_C_algEquiv_pi`
(node `lem-pc-polynomial-quotient-distinct-linear-crt`).
Added zero holes; zero sorries remain in the delivered module. No lemmas were split off.
All four dependencies are proved Mathlib declarations.

## No longer needed

None. All four planned Mathlib dependency nodes are used:
`lem-pc-crt-pairwise-linear-ideals`, `lem-pc-crt-principal-ideal-product`,
`lem-pc-crt-ideal-quotient-product`, and `lem-pc-crt-linear-evaluation`.
All three original imports supply declarations used in the proof. No project module or
DAG node is pruned, and the proof follows the existing node and unit route unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. LeanFinder, Loogle, and the library/Mathlib
text searches confirmed the existing CRT and evaluation ingredients; no single exact
replacement theorem was found. No definition or statement repair was needed.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
