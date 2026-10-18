## What changed

Replaced the proof of `CategoryTheory.Functor.preservesKernel_of_pretriangulated`
in `lean/Sheaf/CategoryTheory/PretriangulatedKernelSplit.lean` with a complete Lean proof.
The argument follows the existing four-step DAG plan and Stacks Project, Derived Categories,
Tag 05QU, proof of (1) implies (3): the kernel inclusion is monic, its distinguished cone
triangle splits, and the complementary component of the original map is monic and splits.
Mapping the resulting identities through the additive functor gives a kernel lift for every
target object; the mapped retraction proves uniqueness.

Mathlib's `Triangle.mor₃_eq_zero_of_mono₁` packages the rotation/exactness calculation in
step 2. `exists_iso_binaryBiproduct_of_distTriang` supplies the compatible splitting.
All imports and declaration signatures are unchanged. No definitions or other modules changed.
The file compiles without warnings through `lcompile.py` (2.5 seconds).

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.preservesKernel_of_pretriangulated`
(node `lem-cor-int-compactness-ii-pretriangulated-kernel-split`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
There are no split-offs and no dependencies on unfinished project theorems.

## No longer needed

None. No imports were removed. Every declared proof dependency is still used through its
Mathlib API: preadditivity, additivity, cone triangles and their rotation/exactness,
biproduct splitting, and the splitting of monomorphisms. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan is implemented without changing the statement or unit route.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
