## What changed

Proved `CategoryTheory.ConstantCompletion.completedPositiveKoszulPullback` in
`Sheaf.Paper.CompletedPositiveKoszulPullback`, preserving its statement and public
import. Added private proved helpers for transport of sections, scalar multiplication,
two-term factor comparisons, tensor naturality, and augmented tensor compatibility.
Proof imports use the existing constant-ring section rigidity, inverse-image section
transport, scalar-extension calculation, ordinary complex tensor pullback, and
monoidal cochain-complex instances. Updated the item's DAG proof and dependencies.
No other existing module or node is changed.

The induction retains the supplied comparison `u`: its degree-zero component
compares the first rank-one factor, while the canonical comparison compares the
tail. This gives the arbitrary-`u` projection equation directly.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ConstantCompletion.completedPositiveKoszulPullback`
(node `lem-sfb-completed-positive-koszul-pullback`).

Holes closed: 1 of 1. Holes added: 0. Sorries remaining in the item: 0.
No split-off statements, axioms, or admitted private helpers were added.

## No longer needed

The separate automorphism-classification and automorphism-extension argument in
old proof step 4 is unnecessary: retaining arbitrary `u` in the tensor induction
replaces it. That step had no separate declared dependency to withdraw.
No existing module, node, or original import is pruned. All three originally
listed proof dependencies remain used. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The theorem is valid, including empty generator lists and zero or repeated
scalars. The old plan omitted the concrete section-transport and scalar-extension
glue, which is now proved using the already available section rigidity and
inverse-image compatibility declarations. Its separate treatment of arbitrary
`u` can be replaced by the stronger induction described above. There are no
statement or definition repairs and no shared-interface changes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
