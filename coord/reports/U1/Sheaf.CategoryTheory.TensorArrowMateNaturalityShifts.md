## What changed

Filled `CategoryTheory.TensorArrowMate.naturality_shifts` in
`Sheaf.CategoryTheory.TensorArrowMateNaturalityShifts`, preserving all signatures,
definitions, docstrings and imports. For fixed K, E and c, the proof packages beta as
mu followed by the whiskered transformation TD.map c. Mathlib's CommShift instances
for composition and whiskering give its shift equation. The corresponding composite
of the adjunction unit with R(beta), including the canonical functor unitors and
associator, is shift-compatible as well. Adjunction.homEquiv_unit identifies its
components with alpha, giving the second shift equation.

For commuting squares, functoriality of TD, the given square, naturality of TD.map c',
and naturality of mu in its two variables give beta's equation. Mathlib's
Adjunction.homEquiv_naturality_left_square transfers it to alpha. This implements the
node's seven steps using the API of its two existing Mathlib leaves.

Searched with msearch.py Loogle (`"CommShift", "whisker"`), LeanFinder (naturality
and shift compatibility of adjuncts), and grep (homEquiv_naturality_left_square and
CommShift.whiskerRight), plus rg on the two library roots. The generic Mathlib APIs
supply the proof; no additional tensor or monoidal assumptions are required.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.TensorArrowMate.naturality_shifts`
(node `lem-weil-pbc-tensor-arrow-mate-naturality-shifts`).
Added zero holes; none remain in the item. No split-off statements.

## No longer needed

None. All original imports remain necessary for the existing public signatures and
definitions. Both declared Mathlib dependencies are used. No nodes or modules are
withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No correction was needed. The hTC hypothesis is unnecessary for these conclusions,
but remains verbatim as part of the existing statement: shifts are only in the
second tensor variable, and fixed-input compatibility is used on TD at c.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
