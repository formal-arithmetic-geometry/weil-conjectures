## What changed

Filled all three theorem proofs in
`lean/Sheaf/CategoryTheory/RightDerivedFunctorOfQuasiIsoResolutions.lean`.
The universal property and the unit's invertibility are extracted from the two
clauses of the specification of the existing chosen universal pair, supplied by
`CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
For uniqueness, surjectivity of the two universal bijections gives comparison
transformations in both directions. Injectivity proves both inverse identities
and uniqueness of the unit-compatible isomorphism.

The proof follows steps 1–3 of `def-sfb-right-derived-functor` without a route
change: Mathlib supplies the triangulated instances for the degreewise additive
functor and localization, the recorded K-injective theorem supplies the pair,
and the existing object-comparison definition composes the stated isomorphisms.
The unit `sk-def-sfb-derived-categories` and its route are preserved.
Only proof bodies changed. All six existing signatures, definition bodies,
visibility, imports, universes, and docstrings are unchanged. No new nodes,
statements, definition repairs, or consumer adaptations are needed.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to
`def-sfb-right-derived-functor`:

- `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal`.
- `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_unique`.
- `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso`.

Holes added: 0. Holes left in the item: 0. Split off: 0.
The existing K-injective total-derived theorem used by the definitions and proofs
is already proved in the shared library. The proof does not assume monomorphic
resolutions, enough injective objects, left exactness of the additive functor,
or a common Hom universe. It also applies to zero complexes and zero categories,
since it only extracts the given universal property and uses category identities.

## No longer needed

None. The single public import
`Sheaf.CategoryTheory.KInjectiveTotalDerived` supplies declarations used by the
existing definitions and the proofs and remains necessary. No imports were added.
All declared dependencies of the node remain used, directly or through the
Mathlib instances: additive functors, abelian categories, homotopy and derived
category triangulations, and the K-injective total-derived theorem. No DAG nodes
or modules are pruned; no node proof update is needed for this unchanged route.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node's proof plan is implemented using
the already proved general theorem, whose chosen-pair specification directly
contains two of the three missing conclusions. The third is exactly the
comparison-and-injectivity argument in step 2. The canonical resolution
isomorphism was already constructed and is retained unchanged.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
