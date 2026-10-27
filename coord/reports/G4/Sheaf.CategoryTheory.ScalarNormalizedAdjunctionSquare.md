## What changed

Proved `CategoryTheory.Adjunction.scalarNormalizedAdjunctionSquare` with its exact existing
signature and public imports. The scalar-unit transpose calculation uses the two normalization
hypotheses, naturality of `b.inv`, the ambient counit hypothesis, and counit naturality.
Injectivity of the scalar adjunction Hom equivalence gives the counit equality. The restricted
adjunction and Mathlib's `mateEquiv_counit` identify beta as the mate of alpha inverse.
`unit_mateEquiv` then gives the unit equality; its inverse transpose is the identity by the
triangle identity. Updated the node's last two proof steps to this equivalent order.

## Proved and sorry left

Closed the single hole in `CategoryTheory.Adjunction.scalarNormalizedAdjunctionSquare`
(node `lem-weil-pbc-scalar-normalized-adjunction-square`). Added zero holes and zero split-off
statements. No sorry remains in the delivered module.

## No longer needed

None. All three existing public imports remain necessary for the theorem statement.
Both planned proof dependencies are Mathlib leaves and are used: the adjunction Hom formulas
and the mate correspondence. No nodes or modules are withdrawn or claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The final two DAG steps are implemented in the opposite order:
identify the mate from the counit first, then use Mathlib's proved unit identity for that mate.
This avoids repeating the internal triangle/naturality calculation and preserves the unit route.
The compile service initially returned exit 124 (no answer after 637 seconds); retried as required.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
