## What changed

Proved `AlgebraicTopology.AugmentedPosetChains.boundary_laws` in
`lean/Sheaf/AlgebraicTopology/AugmentedPosetChains.lean`. The public statements,
definitions, attributes and imports are unchanged. Added proved private helpers
for alternating deletion sums, their cons recurrence, preservation of subtraction,
square-zero identity, and evaluation of the boundary on a strict bracket.

The proof is an induction on the underlying list, generalized over the function
on deleted lists. It then uses strictness and length preservation under deletion
to evaluate the composite on each free generator. Finsupp and linear-map
extensionality extend the identity to every chain. The off-shape clause follows
directly from the boundary definition. Updated the item's DAG proof to record
this argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicTopology.AugmentedPosetChains.boundary_laws`
(node `def-sfb-augmented-poset-chains`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module. All private helpers are proved.

Validation: the required remote single-file compiler passed without warnings
in 2.7 seconds, below the 60-second limit. Delivery preflight checks axioms.

The list induction includes the empty list and the singleton, hence the
augmentation and degrees below -1. It uses no finiteness or nontriviality
assumption, so empty posets, arbitrary universes and the zero ring are covered.

## No longer needed

None. No import was added or removed. The node originally had no proof
dependencies, and the proof requires no new Sheaf or WeilConjectures dependency.
No module or node is withdrawn; the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The definition node's proof field was empty even
though its statement and `boundary_laws` docstring specified double-deletion
cancellation. The delivery supplies that proof directly, using induction rather
than a two-index involution. Search found the general simplicial alternating-face
square-zero lemma, but constructing a simplicial object and identifying its
complex would require more machinery than this direct list proof.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
