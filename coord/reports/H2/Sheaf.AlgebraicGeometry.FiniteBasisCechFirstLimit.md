## What changed

Proved `AlgebraicGeometry.Scheme.AffineProEt.finite_basis_cech_first_limit` in
`Sheaf.AlgebraicGeometry.FiniteBasisCechFirstLimit`, with its signature and all five
existing definitions unchanged. All new helpers are private and fully proved.

The proof constructs maps on ordered intersections by their universal property,
checks their functoriality and compatibility with every face map, and builds the
actual Čech complex diagram and restriction cocone. It proves intersection limits
for the given coordinate presentations, transfers set continuity to module and
abelian coefficients using the existing pullback/forgetful comparison, and proves
the finite product cocones colimiting by representatives and eventual equality.
Degreewise colimits give the complex comparison; extension by zero and exactness
of filtered abelian-group colimits give the two requested families of isomorphisms.

Added private proof imports of `ProEtaleComparisonSections`,
`SheafPullbackForgetComparison`, `Mathlib.Algebra.Category.Grp.AB`, and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`. Updated the item's DAG proof,
proof dependencies and proof origin to this implementation. No public interfaces,
other modules, or source-library declarations were changed.

Validation: the prescribed remote single-file compiler passed (23.4 seconds), and
text comparison confirms the original theorem signature is unchanged. A further
21.0-second compile with `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; the diagnostic command was then removed. All lines
are at most 100 characters. The finite tuple proof permits repetitions, empty
intersection objects, and degree zero; the continuity argument permits
noncommutative coefficient rings and does not assume injectivity of F.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.AffineProEt.finite_basis_cech_first_limit`
(node `lem-weil-pbc-finite-basis-cech-first-limit`).

Added 0 holes; split off 0 statements; 0 `sorry`s remain in the item. Every private
helper is proved. This is a proof, not a decomposition into new unproved lemmas.

## No longer needed

The proof does not use
`lem-weil-pbc-filtered-colimits-commute-finite-limits` or its statement module: its
finite-product special case is proved directly using the concrete filtered-colimit
API. Removed this node from `proof_deps`; the temporarily tried proof import
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` was removed.

The existential presentation/intersection theorem
`exists_finite_intersection_limit_compatibility` is not applied: the theorem here
must work for its supplied presentations, and intersection limits follow directly
from their coordinate limits. The corresponding node and public module import
remain needed for `firstLimitCoordinate` in the existing definitions; they are not
withdrawn or claimed as pruned modules.

The separate `Mathlib.Algebra.Category.Grp.FilteredColimits` import was removed
because `Mathlib.Algebra.Category.Grp.AB` already imports it. Every original public
import remains. No Lean module is withdrawn, and no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original prose said to apply the intersection-compatibility theorem to the
supplied systems. Its declaration instead existentially chooses systems of its
own; it does not directly establish the assertion for arbitrary input systems.
The proved universal-property argument supplies the required result without a
statement change or a new hole. The geometric stage/cover hypotheses are retained
verbatim even though this colimit calculation only uses the coordinate limits,
the basis-valued stages, and classical coefficient continuity.

No tool changes, definition repairs, forced adaptations, or new nodes were needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
