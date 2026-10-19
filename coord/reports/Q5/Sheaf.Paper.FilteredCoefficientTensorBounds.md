## What changed

Proved `AlgebraicGeometry.Scheme.filteredCoefficientTensorComplex_laws` using the
existing change-of-rings shape and composition lemmas together with preservation of
zero morphisms by site sheaf tensoring. Public signatures and definitions are unchanged.

## Proved and sorry left

Closed 1 of the 2 original `sorry`s:
`AlgebraicGeometry.Scheme.filteredCoefficientTensorComplex_laws`.
The remaining `sorry` is
`AlgebraicGeometry.Scheme.filteredCoefficientTensor_constructible_bounds`
(node `lem-sf-filtered-coefficient-tensor-bounds`). No holes were added or split off.

## No longer needed

No repository modules or DAG nodes were pruned. The retained experimental helper
split and its private transport lemmas were removed from the delivered module because
they were not a completed proof and had no DAG nodes. No imports were added or removed.

## Where the brief, the DAG or earlier work was wrong

The differential laws follow directly from the existing termwise change-of-rings
identities and zero preservation; they do not require the finite-filtration argument.
The finite-filtration theorem remains open because the available bounded constructible
triangulated theorem is stated for coefficient rings in `Type u` and the predicate
`IsConstructibleProEtaleModuleSheaf`, while this item uses `Type (u + 1)` and
`IsConstructibleProEtaleCoefficientModuleSheaf`.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
