## What changed

Replaced the proof of
`CategoryTheory.Adjunction.leftCoefficientProjectionMap_coherence` in
`Sheaf.CategoryTheory.Adjunction.LeftCoefficientProjectionAction`.
The proof follows the existing five-step plan. First it calculates the transpose of the
symmetry-conjugated right projection using counit naturality, the existing right projection
transpose theorem, preservation of braiding and symmetry. It then proves joint naturality,
the unit law and the associativity law by injectivity of the adjunction Hom equivalence,
using the oplax tensorator naturality and coherence equations from Mathlib.
The statement, definition, docstrings and imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Adjunction.leftCoefficientProjectionMap_coherence`
(node `lem-pur-adjoint-left-projection-action`).
No holes added, no statements split off, and no sorry remains in the delivered module.

## No longer needed

None. All three existing imports are needed for the statements and the definition.
All three declared proof dependencies remain used through their existing Mathlib
implementations: the adjunction Hom equivalence, monoidal category laws and monoidal
functor coherence. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. LeanFinder, Loogle and Mathlib grep searches confirmed
that the available results supply the ingredients rather than this complete four-clause
statement. The proof follows the node's route without new intermediate statements.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
