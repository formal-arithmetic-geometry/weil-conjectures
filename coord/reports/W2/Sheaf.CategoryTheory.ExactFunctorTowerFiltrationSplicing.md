## What changed

Replaced the proof of `CategoryTheory.exactFunctorTowerFiltrationSplicing` by the finite
inverse-image splicing argument in the existing node. All public declarations and all public
imports retain their original signatures and visibility. The only added import is the private
proof import `Mathlib.Order.Fin.Basic` for monotonicity of finite sequences.

The private helpers identify the cokernel between two inverse images along an epimorphism,
compare the quotients of represented images and exact-functor images, and concatenate the two
filtrations at their common kernel step. The tower filtration and the composite functors are
constructed explicitly using `Fin.reverseInduction`. The length computation and ordered label
transport are separate finite inductions. No section of an epimorphism and no unspecified
existence witness is chosen.

## Proved and sorry left

Closed: `CategoryTheory.exactFunctorTowerFiltrationSplicing`
(node `lem-zl-exact-functor-tower-filtration-splicing`), the item's one original hole.
Added: none. Remaining: none. Every private helper has a complete proof.

Validation: the full source with `#print axioms` compiles cleanly in 16.6 seconds.
The theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
The public theorem signature is byte-for-byte identical to the original, and every line
is at most 100 characters.

## No longer needed

Removed redundant private imports `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
and `Mathlib.Algebra.Homology.ShortComplex.Exact`, already publicly provided by
`Mathlib.CategoryTheory.Abelian.Exact`. No declared proof dependency is pruned. The proof uses the existing represented-subobject
comparison `CategoryTheory.Subobject.cokernelOfLEMkIso` and Mathlib's cokernel preservation,
refinement, and exact-epi-cokernel results corresponding to the node's dependencies.
No module or node is withdrawn. The searches found no existing theorem stating the full tower
with prescribed subobjects, ordered factors, and labels.

## Where the brief, the DAG or earlier work was wrong

None. The proof follows the existing six-step argument. The stability of epimorphisms under
pullback is supplied directly by Mathlib's `Abelian.epi_fst_of_isLimit`; exactness of successive
inverse-image inclusions is proved with the prescribed refinement criterion. Zero-length
blocks use the kernel junction equality, and the terminal filtration uses the assumed zero
object, so neither degenerate case needs an extra hypothesis.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
