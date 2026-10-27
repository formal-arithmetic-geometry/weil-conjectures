## What changed

Proved `TopCat.Sheaf.isZero_siteCech_of_surjective_unions` without changing its signature.
Private helpers construct the auxiliary upper-set space of finite nonempty subsets, the
union-of-intersections functor on opens, its continuity, and a componentwise complex isomorphism.
The proof follows Stacks Project Tag 0A36, `lemma-vanishing-ravi`, and applies the existing proved
flasque Čech theorem (Tag 09SZ). The finite-point variant has all the principal opens used in
Stacks' argument and makes their smallest-neighborhood property immediate. Universe lifting
puts the auxiliary space and coefficients in `max v w`, preserving independent `u`, `v`, `w`.
The existing node's proof fields record this variant.

## Proved and sorry left

Closed: `TopCat.Sheaf.isZero_siteCech_of_surjective_unions`
(node `lem-sfb-cech-vanishing-surjective-unions`), one original hole.
Added holes: none. Remaining holes in this delivery: none. No new public declarations.
Single-file server compile passed in 3.7 seconds, with no warnings.

## No longer needed

`lem-weil-pbc-site-continuous-pushforward-sheaf` and its module
`WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf` are not needed by this proof.
Mathlib's `Functor.isContinuous_of_coverPreserving` and `Functor.op_comp_isSheaf` prove
precomposition is a sheaf directly from the intersection and cover calculations.
The corresponding obsolete `tool_uses` entry is removed. The source declaration itself is
preserved in the library. No modules are withdrawn. All other declared dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original infinite-subset auxiliary space may be replaced by
finite nonempty subsets, with the same basic-open intersection and section formulas. No unit
route changes. The attached flasque theorem requires its coefficient and space universes to
agree; explicit ULift constructions handle this without changing the item's universes.
The continuous-site dependency is a valid alternative but Mathlib's direct criterion suffices.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
