## What changed

Filled the two functor-law proofs in
`Sheaf.CategoryTheory.YonedaExtOneFunctor`, following their existing proof docstrings.
Both proofs use extensionality of group morphisms and the existing additive comparison.
The identity proof rewrites `Functor.map_id` and cancels the comparison with its inverse.
The composition proof rewrites `Functor.map_comp` and cancels the middle comparison.
The comparison's recorded group instances are installed locally for elaboration.
Statements, definitions, imports, and the unit route are unchanged.

## Proved and sorry left

Closed both original holes (2 of 2):

- `CategoryTheory.YonedaDerivedExtComparison.yonedaExtOneMap_id`.
- `CategoryTheory.YonedaDerivedExtComparison.yonedaExtOneMap_comp`.

Both belong to `def-sfb-yoneda-ext-one-functor`.
No holes remain in the item. No holes were added or split off.

## No longer needed

None. The only import, `Sheaf.CategoryTheory.YonedaDerivedExtComparison`, supplies
the structure and comparison used by the existing public definitions and both proofs.
The node has no planned proof dependencies to prune. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The existing docstrings give the complete argument.
The proof works uniformly, including zero objects, zero morphisms, and trivial groups,
and needs no existence theorem for the comparison because the datum `c` is supplied.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
