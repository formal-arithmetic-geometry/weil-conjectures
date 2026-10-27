## What changed

Filled `CategoryTheory.Functor.additiveDerivedPlus_unit_normalization` in
`Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization` without changing its
signature, definitions, public imports or existing docstrings.

The full derived pair's existing universal property supplies the first clause.
Its invertible K-injective units and localization supply the full value
isomorphisms. For the comparison, apply Mathlib's injective derivability criterion
`LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso` to both the restriction
of the full pair and the inclusion of the given bounded-below pair. The criterion
requires exactly invertibility of their units on bounded-below injectives, which
follows from K-injectivity and the bounded-below derived unit theorem. Then
`Functor.rightDerivedUnique` constructs the comparison, its factorization equation
normalizes the units, and `rightDerived_ext` proves uniqueness. Boundedness follows
by transport across its components. Both resolution formulas follow by cancellation
in naturality equations. The full value formula uses unit naturality and the given
commutative square, so it requires no choice of a homotopy lift.

Updated the item's DAG proof, proof dependencies and proof origin to describe this
shorter argument. No additional imports, declarations, modules or nodes are needed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.additiveDerivedPlus_unit_normalization`
(node `lem-sfb-additive-derived-plus-unit-normalization`).

Holes added: zero. Holes remaining in this delivery: zero. No split-off statements.
This is a proof from existing declarations, not a decomposition. The transitive
axioms will be checked by the delivery probe.

## No longer needed

No Lean import was removed: the two existing public imports are needed by the
statement and proof. No source-library declaration or module is withdrawn.

The following planned dependencies are no longer direct dependencies of this node:

- `lem-weil-pbc-dplus-injective-representative`: no representatives are selected;
  Mathlib's injective derivability structure supplies the comparison criterion.
- `lem-weil-pbc-kinjective-hom-derived`: no homotopy lifts are selected; naturality
  of the comparison is already part of `rightDerivedUnique`, and the full formula
  assumes its commutative square explicitly.
- `lem-pur-homotopy-category-triangulated` and
  `lem-weil-pbc-kinjective-total-derived`: the recorded derived pair already has
  the needed universal property and unit invertibility. These remain transitive
  prerequisites through `def-sfb-right-derived-functor`; they are not claimed as
  removed from the targets' closure.
- `def-sp-left-exact-additive`: additivity is used through the existing functors
  and pair; no separate cone calculation is repeated here.

Removed the obsolete direct tool approvals for the four listed tool nodes
(the representative, Hom-bijection, triangulated and total-derived tools).
The node now cites `def-sfb-right-derived-functor` directly for its proved API.
The bounded-below derived pair, bounded-below K-injectivity and derived boundedness
nodes remain. The unit's restricted-functor route and all ancestor statements stay.
No whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement needs no repair. The DAG plan did more work than
necessary by explicitly constructing components on representatives and lifting
morphisms. The existing Mathlib injective derivability criterion encapsulates that
argument and applies with target the full derived category. In particular it does
not require the stronger monomorphic K-injective-resolution typeclass used by the
upstream full-to-plus comparison.

Searches run through msearch: LeanFinder for bounded-below unit comparison; Loogle
for `rightDerivedUnique`; grep for `isRightDerivedFunctor_of_isIso`,
`rightDerivedUnique` and `rightDerivedFunctorPlusCompatibility`. Read the exact
Mathlib criterion, bounded-below injective instances, right-derived uniqueness API,
and upstream PlusCompatibility proof before implementing this specialization.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
