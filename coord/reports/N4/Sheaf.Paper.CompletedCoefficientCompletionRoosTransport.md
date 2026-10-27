## What changed

Proved `WeilConjectures.completedCoefficientCompletionRoosTransport` with its existing
signature and normalization hypothesis. Only its module and proof-route node are changed.

The proof first constructs the normalized Roos triangle for the actual PBC completion.
It compares a K-flat strict reduction tower with the derived quotient reductions using
the specified evaluation counits, and preserves the completion unit under the Koszul
comparison. It then uses the normalized integral coefficient presentation comparison.
Uniqueness of left adjoints identifies the PBC and detailed scalar-extension choices;
a local adjunction calculation proves compatibility of their transitions. Exact derived
restriction reflects the triangle, and product extensionality proves the unit equation.

All added imports are private proof imports. Local helpers are proved; no public API,
definition or consumer signature changes.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.completedCoefficientCompletionRoosTransport`
(node `lem-pur-completed-coefficient-completion-roos-transport`).
No holes added, no statements split off, and no `sorry` remains in the delivered module.
The proof uses existing declarations with their existing dependency assumptions.

## No longer needed

No modules are withdrawn. The three original public imports are retained.
The proof reuses the intrinsic PBC part of the existing completed Koszul Roos proof,
rather than constructing another constant-presentation model. Existing dependencies of
that module remain needed and are not proposed for withdrawal.

The item no longer needs direct route edges to `def-weil-pbc-intrinsic-completion`
and `lem-weil-pbc-constant-completion-equivalence`: the existing
`actualCompletion_quotient`, `completedKoszulQuotientComparison`, and
`actualFiberToStrict` interfaces provide the unit-normalized comparison directly.
Their modules remain in the library and may remain transitive dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The detailed transition-comparison module cannot
be imported here because its import closure already contains this item. The proof
therefore derives the necessary compatibility locally from the lower-level normalized
DVR K-flat transition theorem and uniqueness of adjoints. The mathematical route and
the blueprint unit route are preserved.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
