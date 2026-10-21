## What changed

Filled both theorem proofs in `Sheaf.CategoryTheory.JointAdjunctionModelEmbedding`, preserving
all signatures, docstrings, and imports. The model theorem follows the node's six-step argument:
project the kernel equation to each factor, compare adjuncts using naturality, cancel the local
model isomorphism, and use preservation of the kernel to make its zero image arrow monic.
`IsZero.of_mono_eq_zero` supplies local zero objects; joint zero detection and
`Preadditive.mono_of_isZero_kernel` conclude. The latter Mathlib lemma implements the node's
kernel-factorization cancellation argument. The unit theorem specializes to identity isomorphisms.

The proof uses only the existing Mathlib imports, with no further Sheaf dependencies.
The completed module compiled cleanly through `lcompile.py` in 6.1 seconds.
LeanFinder, Loogle, and source searches found the needed elementary kernel and zero-object API,
but no direct theorem for this jointly detecting family. The proof treats arbitrary index types;
in particular an empty family is handled by the given zero-detection hypothesis.

## Proved and sorry left

Closed both original holes (2 closed, 0 added):

- `CategoryTheory.mono_pi_lift_adjunction_models`.
- `CategoryTheory.mono_pi_lift_adjunction_units`.

Both belong to `lem-sfb-joint-adjunction-model-embedding`. No sorry remains in the module,
and no new module, axiom, or intermediate sorry is added.

## No longer needed

None. All four declared dependencies are Mathlib definition leaves used by the unchanged proof
route: `def-weil-category-product`, `def-sp-abelian`, `def-weil-pbc-additive-functor`, and
`def-weil-preadditive-category`. All existing imports serve the statements or the proof; none
is removed. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the recorded kernel-and-adjunction argument without changing the unit
route or any statement. Mathlib's zero-kernel criterion packages steps 4–5 of that argument.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
