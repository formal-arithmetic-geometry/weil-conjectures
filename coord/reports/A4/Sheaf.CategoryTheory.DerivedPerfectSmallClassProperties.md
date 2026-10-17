## What changed

The target theorem `CategoryTheory.derived_perfectSmallClass_properties` is now proved from two
strictly smaller categorical interfaces.  The proof factors maps through finite subcoproducts,
uses finite coproduct lifting, and then applies `hSsum` for the bounded-subcoproduct conclusion.
The delivery adds `Sheaf.CategoryTheory.DerivedPerfectSmallClassFactorization` and
`Sheaf.CategoryTheory.DerivedPerfectSmallClassFiniteLifting`, and updates the target node's proof
route and dependencies accordingly.

## Proved and sorry left

Proved: `CategoryTheory.derived_perfectSmallClass_properties` (the original target hole).

Sorry left: `CategoryTheory.derived_factor_through_small_subcoproduct`, node
`new-sfb-derived-perfect-small-class-factorization`.  The finite lower-level theorem
`CategoryTheory.derived_finite_coproduct_surjective` (node
`new-sfb-derived-perfect-small-class-finite-lifting`) is proved by the finite biproduct argument.
The remaining split is the finite-support factorization for an alpha-presentable Hom functor.

## No longer needed

No stated proof dependency was removed.  The target uses the existing derived coproduct theorem
through the local derived coproduct instance, and the two new modules are the only additional
imports used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan described a single filtered subcoproduct argument but did not expose the
finite-support and finite-biproduct interfaces needed by Lean.  The target statement itself was
unchanged; the DAG was refined with the two strictly simpler intermediate nodes.

## New nodes

`new-sfb-derived-perfect-small-class-factorization` is stated in
`lean/Sheaf/CategoryTheory/DerivedPerfectSmallClassFactorization.lean` and records the finite
subcoproduct factorization required by alpha-presentability.

`new-sfb-derived-perfect-small-class-finite-lifting` is stated in
`lean/Sheaf/CategoryTheory/DerivedPerfectSmallClassFiniteLifting.lean` and records the finite
biproduct lifting argument for componentwise surjections.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
