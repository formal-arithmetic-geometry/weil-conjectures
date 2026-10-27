## What changed

Replaced the proof of
`CategoryTheory.CompositorEquivalenceConjugation.pasting_conjugation` in
`Sheaf.CategoryTheory.CompositorEquivalenceConjugation` with the node's componentwise
calculation. The pair and identity squares are evaluated at objects; naturality proves
the two triple and two unit pasting equations; inverse cancellation gives conjugation,
and faithfulness of the equivalences reflects associativity and identity equations.
All definitions, signatures, public imports and the existing dependency route are preserved.

## Proved and sorry left

Closed the sole existing hole in
`CategoryTheory.CompositorEquivalenceConjugation.pasting_conjugation`
(node `lem-sfb-compositor-equivalence-conjugation`). No holes are added or split off.
No `sorry` remains in the item. The final module compiled through `lcompile.py`
in 3.8 seconds with no errors or warnings. The delivery preflight also checks axioms.

## No longer needed

None. The proof follows the existing ten-step node and retains its Mathlib faithfulness
leaf `def-sf-induced-category`. No imports, nodes or modules are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The Mathlib searches found adjunction mate formulas
and results about already coherent pseudofunctors, which do not directly prove this
statement for arbitrary compositor and unit data. The direct defining-equation argument
in the existing node suffices.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
