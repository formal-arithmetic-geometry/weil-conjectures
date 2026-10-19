## What changed

Completed the retained proof of
`CategoryTheory.geometric_inverse_image_constant_module` without changing any public
signature or definition. The proof constructs the comparison of constant set sheaves
from their coproducts of points, proves its naturality, and lifts it to abelian sheaves
using `AddCommGrpCat.leftExactFunctorForgetEquivalence`. Naturality for scalar linear
endomorphisms, the inverse-image scalar equation, and locally surjective restriction
of scalars make this comparison a module morphism. Forgetting to sets reflects
isomorphisms. The last equation follows from the coproduct injection equation after
cancelling the sheafification comparisons and reassociating the composites.

All added helpers are private and fully proved. Updated the node's proof steps and
proof dependencies to describe the implemented scalar argument. The original public
imports are retained; proof imports add Mathlib's left-exact additive-functor API and
module biproducts.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.geometric_inverse_image_constant_module`
(node `lem-sfb-geometric-inverse-image-constant-module`).
Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivered module.
The existing theorem `CategoryTheory.constant_left_module_inverse_image` remains
an admitted dependency in its own module; this delivery uses its declared interface.

The complete module compiled through `lcompile.py` in 12.5 seconds with exit code 0
and no warnings. The resumed session repaired stale namespace references:
`LeftExactFunctor.of` and `Functor.whiskerRight` / `Functor.isoWhiskerLeft` /
`Functor.isoWhiskerRight`. The required dry run checks the declaration probe and
delivery preflight before pushing.

## No longer needed

Removed the redundant proof imports `Mathlib.CategoryTheory.Sites.Sheafification`,
`Mathlib.CategoryTheory.Sites.PreservesSheafification`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and
`Mathlib.CategoryTheory.Adjunction.Limits`, and
`Sheaf.CategoryTheory.RingedSiteModules`: their APIs are already available through
the public imports. The tentative additional import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` is likewise unnecessary.

Removed `lem-cbc-module-sheafification-underlying-sets` from this node's proof
dependencies. That lemma treats sheafification of presheaves valued in a fixed
`ModuleCat`; the implemented proof instead uses the genuine module sheafification's
underlying abelian sheaf and the abelian forgetful sheafification comparison
`lem-pc-sites-sheafification-underlying-sets`. No project module is withdrawn, and
all remaining declared proof dependencies are used. No unit statement or proof step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction is required. The earlier sandbox had almost the entire proof,
but its final constant-section calculation did not compile. The retained proof repairs that calculation by explicitly cancelling the natural
isomorphism, reassociating, and displaying the composite functor map. The resumed
dry run additionally found stale namespace references; qualifying whiskering in
`Functor` and using `LeftExactFunctor.of` restores compilation against current Mathlib. The source for the scalar variant is Stacks Sites, Tag 00YV (6),
whose proof describes a fixed-ring module by its abelian operations and the scalar
endomorphisms. The coproduct route is unchanged. The node records the Mathlib
left-exact-functor argument used for additivity instead of spelling out binary
operations individually.

Edge cases remain covered: the point cofan proof works for the empty index type;
zero modules, the zero ring, empty sites and identity inverse image require no
extra hypotheses. No finiteness assumption on the coefficient module is introduced.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
