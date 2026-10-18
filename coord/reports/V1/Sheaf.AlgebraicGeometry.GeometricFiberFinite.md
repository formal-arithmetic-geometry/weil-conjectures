## What changed

Proved both existing theorems of `Sheaf.AlgebraicGeometry.GeometricFiberFinite` with
unchanged signatures and public imports. The derived clause directly specializes the
source library's module-valued proper base change using `isAddTorsion_of_finite` and
`moduleTorsionHomology_of_isTorsion`.

The stalk clause constructs the source comparison from exact inverse image, the canonical
module-valued identity germ, and `upperStarCompSheafFiberIso`. The private identity-germ
helpers are fully proved by forgetting to the existing set-valued constancy theorem,
commuting filtered stalk colimits with the forgetful functor, and reflecting isomorphisms.
The target comparison uses exact global sections over Spec Omega, the canonical generic
module-valued Leray isomorphism, bounded-below/unbounded compatibility, and compatibility
of inverse image with single complexes. Homology and global sections preserve the specified
exchange isomorphism; composition with these two comparisons proves the required map invertible.

Updated the existing node's proof, proof dependencies and origin to follow this argument.
Removed the obsolete bounded-below Leray tool approval. The generic source-library Leray
implementation recorded at `lem-kun-leray-unbdd` is used as a tool in its stronger, arbitrary
module-coefficient form (the declaration itself has no coefficient or dimension restriction).
`src-right-derived-functor-plus-compatibility` is the existing generic compatibility tool.
These realize the same Leray step of the original argument; no unit statement or step is bypassed.
No new statement, definition repair, consumer adaptation or change record is needed.

Validation: both theorems compile through the required remote single-file compiler, including
both proved private helpers, after pruning. Checked the source Tag 0DDF and current blueprint
statement and proof. The proof handles the zero ring, zero sheaf, degree zero and empty fibres
without additional assumptions: all comparison functors are defined in these cases. The
finite-sheaf hypothesis is retained unchanged and unused, as the original proof anticipated.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.Etale.isIso_geometricFiber_finite`.
- `AlgebraicGeometry.Etale.geometricFiber_finite_stalk_formula`.

Both realize node `cor-weil-pbc-geometric-fiber-finite`.
There are zero `sorry` left in the item, zero holes added, and zero split-offs.
This is a proof from existing library declarations; the proper-base-change theorem used
remains an existing project dependency, with no claim here to have eliminated its holes.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: the standard IsPullback square suffices;
  node `def-weil-pbc-cartesian-square` is not a proof dependency.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`: node
  `lem-weil-pbc-exchange-forget-coefficients` is unnecessary because module-valued proper
  base change is already available.
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`: the abelian canonical global-germ
  theorem is unnecessary; its publicly imported `GeometricPointPullbackStalk` module is
  imported directly for exactness. The node remains needed for that original module clause.
- `Sheaf.AlgebraicGeometry.LerayBounded`: node `lem-kun-leray-bdd` and its abelian-only wrapper
  are unnecessary because the generic module-valued Leray implementation supplies the
  required comparison directly, with PlusCompatibility bridging the two derived conventions.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: no set-sheaf predicates are used.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: duplicate private import of an
  already public import.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: redundant proof-only import.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: redundant proof-only import.

All original public imports are retained. Added only private proof imports for the existing
point-equivalence/constancy, stalk, Leray, exact-functor and PlusCompatibility APIs.
No other planned proof dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a reduction from module coefficients to abelian coefficients, but the current
source library already provides the module-valued bounded-below proper-base-change theorem.
That makes the forgetting-coefficients comparison unnecessary here. The bounded-below Leray
wrapper is specialized to abelian sheaves; the existing generic module-valued comparison,
with the already stated PlusCompatibility isomorphism, gives exactly the required target.
The original theorem statements and their meanings are unchanged.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
