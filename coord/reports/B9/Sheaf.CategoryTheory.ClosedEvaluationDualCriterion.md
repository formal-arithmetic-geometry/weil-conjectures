## What changed

Completed `CategoryTheory.closed_evaluation_dual_criterion` in
`Sheaf.CategoryTheory.ClosedEvaluationDualCriterion`, preserving both definitions and the
entire theorem signature. Added the proof-only import
`Mathlib.Tactic.CategoryTheory.Monoidal.Basic` for monoidal coherence calculations.

The proof implements the existing node's four steps. First, cancellation of the comparison
against its inverse gives the defining equation for the specified coevaluation. Naturality
and injectivity of the supplied adjunction transpose give the first triangle. Next, monoidal
coherence identifies the transpose of evaluation with the inverse right unitor followed by
the comparison at the tensor unit. For the second triangle, an explicit application of
`whisker_exchange e e` interchanges the two disjoint evaluations; coherence identifies the
result with the first triangle tensored with D. Finally, transposition and cancellation of
the isomorphism at the tensor unit give the second triangle.

The file compiled successfully through `lcompile.py` (1.8 seconds reported by the server).
The existing DAG proof and dependencies describe this proof unchanged, so no node edits
are necessary. No target, definition, statement, or consumer is changed.

## Proved and sorry left

Closed the single hole in `CategoryTheory.closed_evaluation_dual_criterion`
(blueprint: `lem-fix-closed-evaluation-dual-criterion`). Both conjuncts are proved.
Holes closed: 1. Holes added: 0. Sorries left in the item: 0. Split off: 0.

## No longer needed

None. No imports were removed and no nodes or modules were pruned. The sole declared
proof dependency, the Mathlib monoidal-category node `def-sfb-monoidal-category`, is used
throughout. All four planned steps and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The source, Stacks Project Tag 0FPU,
`example-dual-derived`, omits these two checks; the existing node supplies a valid abstract
argument, now fully formalized. Existing Mathlib exact-pairing triangle lemmas assume a
pairing, so they do not directly establish this criterion. No additional hypotheses,
symmetry, or pre-existing dual-pair instance are used.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
