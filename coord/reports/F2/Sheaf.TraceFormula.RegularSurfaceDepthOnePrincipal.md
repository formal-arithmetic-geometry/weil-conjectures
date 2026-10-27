## What changed

Proved `RingTheory.regularSurfaceDepthOnePrincipal` with its signature unchanged.
The proof chooses regular parameters to exclude the zero ideal, uses the existing
regular-local UFD theorem and Mathlib's `Finset.extract_gcd`, then applies
`RingTheory.coprimeGeneratorsMprimaryOrUnit` to the residual generators.
In the maximal-radical case, depth one supplies a regular quotient element;
a power of its lift belongs to the residual ideal, and cancellation puts the
gcd in the original ideal. Three proved private helpers provide parameters,
the lower depth bound, and the regular quotient element. The item's DAG proof
and dependency list now describe this argument. No definitions or statements changed.

Added proof import `Mathlib.Algebra.GCDMonoid.Finset`; retained the parameter,
UFD and coprime-generator proof imports. All public imports are unchanged.

Searches used LeanFinder for the principal-kernel statement, Loogle for
`Finset.extract_gcd`, and the grep service for `principal.*depth|depth.*principal`,
as well as local searches through Mathlib and both library roots.
LeanFinder returned dimension-drop results which assume a principal ideal;
Loogle found the exact finite-family gcd extraction theorem.

## Proved and sorry left

Closed the one original hole, `RingTheory.regularSurfaceDepthOnePrincipal`
(node `lem-trf-regular-surface-depth-one-principal`). No holes added, none left
in the delivered module, and no split-off statements. The proof uses the already
stated coprime-generator dichotomy; its existing hole is outside this delivery.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.IsRegularScheme`,
`WeilConjectures.RingTheory.DepthLeSupportDimension` and
`WeilConjectures.RingTheory.AnnihilatorAssociatedPrimesExactSequence`.
The scheme predicate is unused in this ring theorem. Only the lower bound
on the depth of a regular surface is needed to exclude I=0, so the depth/support
dimension upper bound is unnecessary. Direct cancellation avoids cyclic
submodule support and all associated-prime arguments.

Removed DAG proof dependencies
`lem-weil-pbc-depth-le-support-dimension`,
`lem-weil-pbc-associated-primes-exact-sequence`,
`lem-weil-pbc-minimal-support-prime-associated`, and
`lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes`.
The two latter Mathlib leaves never required explicit imports in the original
module. This reports pruning from this proof; it makes no global withdrawal
claim for dependencies which other modules may still use. No modules withdrawn.
The ring-definition node `def-weil-regular-scheme` remains needed by step 2.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but uses more machinery than needed:
depth at least two suffices for the first step, and the final maximal-associated-
prime obstruction can be replaced by cancellation by a power of a regular
element. The unit statement and its route are preserved. The displayed theorem
signature and original docstring remain unchanged; the precise streamlined proof
is recorded in the updated DAG and above. No interface repairs or new nodes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
