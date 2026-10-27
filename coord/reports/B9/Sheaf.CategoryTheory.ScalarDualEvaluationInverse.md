## What changed

Completed `CategoryTheory.ScalarDualEvaluation.scalarDualEvaluationInverse` in
`Sheaf.CategoryTheory.ScalarDualEvaluationInverse`, preserving its statement and the two
existing definitions verbatim. Added proved private helpers for tensor arithmetic,
restriction, section expansions, evaluation, and the inverse morphism.

The proof follows the existing six-step DAG plan. Mathlib's
`Module.Finite.exists_comp_eq_id_of_projective` supplies the finite free splitting.
The finite-power inverse formula from `constantFiniteFreePresentationExtension` gives
expansions of all sections of the two split retracts. The finite sum defines a linear
and natural inverse. Its composites are calculated on constant generators and extended
to all sections using those expansions. Uniqueness gives independence of the splitting.

Private proof imports access the existing finite-power construction and scalar-extension
arithmetic, together with Mathlib's finite-projective splitting theorem. No public
imports, target statements, source-library declarations, or DAG routes are changed.

Validation: the complete module compiled through `lcompile.py` in 46.7 seconds,
with exit code zero and no warnings. All added helpers have complete proofs. A private irreducible inverse morphism
and its proved section formula avoid repeatedly unfolding its naturality proof
during the final assembly.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ScalarDualEvaluation.scalarDualEvaluationInverse`
(node `lem-sfb-scalar-dual-evaluation-inverse`). Added zero holes; split off zero
statements. No `sorry` remains in this delivery.

The proof uses only the unconditional finite-power part of the presentation-extension
theorem. It assumes neither flatness nor a positive rank. The finite sums and split
identities include rank zero, the zero module and zero coefficient rings.

## No longer needed

None. Every declared mathematical dependency in the six-step plan remains in use.
No module or DAG node is withdrawn, and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The DAG's finite-free/direct-summand argument is
implemented without any additional existence assumptions. Mathlib already packages
the finite generation and projective lifting step into a single theorem.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
