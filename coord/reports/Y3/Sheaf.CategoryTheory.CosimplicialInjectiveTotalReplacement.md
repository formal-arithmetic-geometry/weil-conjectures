## What changed

Proved `CategoryTheory.exists_cosimplicial_injective_total_replacement` without changing
its statement. The proof follows the existing five-step DAG plan. Private proved helpers
restrict a quasi-isomorphism between complexes zero below zero to natural degrees,
identify a natural-indexed complex with its extension followed by restriction, obtain
the nonnegative resolution from the existing bounded-below resolution theorem, and
verify naturality of the signed total-flip isomorphism on each coprojection.

The Grothendieck functorial monomorphism/right-lifting factorization supplies the
functorial injective embedding. Postcomposition and naturality supply both the strict
map and augmentation equations. Column comparison applies to the flipped alternating
bicomplex, whose double flip has precisely the supplied component quasi-isomorphisms;
the signed total-flip isomorphisms then transfer the result to the alternating total.
The summand-sign formula specializes Mathlib's existing total symmetry lemma.

Added a private proof import of
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` for the canonical
stupid-truncation inclusions and their naturality. No public interface, definition used
by another module, source-library declaration, or DAG route changes.

## Proved and sorry left

Closed the single original hole in
`CategoryTheory.exists_cosimplicial_injective_total_replacement`
(node `lem-sfb-cosimplicial-injective-total-replacement`).
Holes closed: 1. Holes added: 0. Split off: 0. Sorries left in the delivery: none.

## No longer needed

None. Every declared proof dependency is used along the original route; no imports,
nodes, or modules are withdrawn. All existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. Restricting an integer-indexed
quasi-isomorphism to natural degrees needs the zero lower-bound hypothesis, especially
at degree zero; the private restriction lemma proves this using the isomorphism from
the supported stupid truncation, rather than assuming arbitrary restriction preserves
homology.

The literature checked was Stacks `derived.tex`,
`lemma-functorial-injective-resolutions` and `remark-match` (Tag 0141), and `homology.tex`,
`section-double-complex` and `lemma-double-complex-gives-resolution` (Tags 012X/0133).
The current blueprint unit and its unchanged realized route were also read.
LeanFinder, Loogle, and grep searches were run through `msearch.py`: Mathlib provides
the component total-symmetry lemmas but no shorter theorem proving the whole statement.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
