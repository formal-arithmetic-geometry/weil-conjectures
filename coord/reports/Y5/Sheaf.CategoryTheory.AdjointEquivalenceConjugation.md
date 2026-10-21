## What changed

Filled the four categorical calculations in
`Sheaf.CategoryTheory.AdjointEquivalenceConjugation` using Mathlib's existing
adjunction and equivalence APIs. Statements, definitions, universes and public
imports are preserved. The argument follows the node's counit, transpose and
naturality calculations.

## Proved and sorry left

Closed four original holes: `CategoryTheory.AdjointEquivalenceConjugation.conjugation_counit`,
`CategoryTheory.AdjointEquivalenceConjugation.conjugation_transpose`,
`CategoryTheory.AdjointEquivalenceConjugation.conjugation_comparison_naturality`, and
`CategoryTheory.AdjointEquivalenceConjugation.conjugation_compositor_naturality`.
All four belong to `lem-pur-adjoint-equivalence-conjugation-calculus`.
Holes closed: 4. Holes added: 0. Holes remaining: 0. No split-off statements.

The counit formula expands `Adjunction.comp_counit_app` twice. The transpose
expands the inverse Hom bijection, cancels the mapped equivalence counits,
and uses counit naturality and the reverse triangle. Both coherence equalities
are proved componentwise by naturality and functoriality.

Validation: single-file compilation via `lcompile.py`; delivery preflight also
checks the axioms of all four declarations.

## No longer needed

None. The sole import, `Mathlib.CategoryTheory.Adjunction.Basic`, remains necessary.
Both declared dependencies, `def-nagata-category` and
`def-weil-pbc-composite-adjunction`, are Mathlib leaves used by the proof.
No additional Sheaf or source-library module, new node, or split-off lemma is needed.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

None. Mathlib defines horizontal composition using the other of the two equal
component formulas; naturality gives the same square in the reverse order.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
