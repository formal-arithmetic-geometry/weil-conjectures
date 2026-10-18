## What changed

Replaced the proof of `Rep.discreteRep_abelian_structure` with a complete construction.
The proof defines the open-stabilizer property, proves closure under subobjects, quotients,
zero objects and finite products, and applies Mathlib's abelian full-subcategory theorem.
It then derives finite limit and colimit preservation from kernel and cokernel preservation,
and reflects exactness through the faithful forgetful functor. Added proof-only imports of
`Mathlib.CategoryTheory.Abelian.Subcategory`, `Mathlib.CategoryTheory.Preadditive.LeftExact`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.Topology.Algebra.OpenSubgroup`.

## Proved and sorry left

Closed the sole sorry, `Rep.discreteRep_abelian_structure`. No sorries were added.
The module compiles without warnings (3.8 seconds with the axiom probe).
`#print axioms Rep.discreteRep_abelian_structure` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Edge cases are covered directly: the empty product uses joint injectivity of its limit
projections, the zero object has a subsingleton carrier, and quotient representatives
are obtained from the surjectivity characterization of epimorphisms in `Rep`.

## No longer needed

None. The existing declaration dependency `def-sp-abelian` is realized by Mathlib's
`CategoryTheory.Abelian`; all existing public imports remain needed for the statement or
proof.

## Where the brief, the DAG or earlier work was wrong

Nothing found. The proof follows the stated open-stabilizer kernel, cokernel, biproduct and
exactness route, using Mathlib's equivalent full-subcategory criterion.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
