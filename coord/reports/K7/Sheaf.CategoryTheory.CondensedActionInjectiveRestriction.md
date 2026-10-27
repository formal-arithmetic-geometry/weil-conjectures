## What changed

Proved `Profinite.CondensedAction.action_injective_restriction` in
`Sheaf.CategoryTheory.CondensedActionInjectiveRestriction`, with its signature unchanged.
The proof uses the injective-preservation conjuncts of the existing forgetful and
product-induction statements. Projection inflation preserves monomorphisms, so the
specified adjunction makes every supplied product-invariants functor preserve injectives.
Mathlib supplies nonnegative resolutions, injective terms in every integer degree,
and K-injectivity of the original resolution. Its bounded-below injective-complex
lemma applies to the invariant complex. The final isomorphism is the derived image
of the resolution augmentation followed by the canonical comparison on a K-injective
complex. No construction or public import changed.

Removed three unused private proof imports and updated the node's proof steps 5–7,
proof dependencies, proof origin, and obsolete `lem-sp-kinjective-computes` tool-use entry.
The other three statement proofs and their original plans remain unchanged.

Validation: the complete modified module compiled without diagnostics in 18.4 seconds
through `lcompile.py`. The argument covers every integer degree and uses no
nonzero-ring or nontrivial-group hypothesis.

## Proved and sorry left

Closed 1 of the original 4 holes:
`Profinite.CondensedAction.action_injective_restriction`.
Added 0 holes and split off 0 statements. This is a proof from existing stated
induction results, which themselves still contain sorry.

The 3 remaining holes, all in node
`lem-sfb-condensed-action-injective-restriction`, are:

- `Profinite.CondensedAction.restriction_free_flat_comparison`;
- `Profinite.CondensedAction.forget_tensor_induction`;
- `Profinite.CondensedAction.product_tensor_induction`.

All remain whole named theorem proofs; no definition contains a hole.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.KInjectiveComputes`: the proved upstream
  `Functor.rightDerivedFunctorObjQIso` supplies exactly the needed unbounded
  derived-category comparison. Node `lem-sp-kinjective-computes` is removed from
  this node's proof dependencies and approved tool uses.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`: no
  completed proof here invokes it. Its node `lem-pc-sites-modules-j-shriek-flat`
  remains in the unproved free-flat comparison's original plan.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: no completed proof
  needs this extra private import. The existing public statement imports already
  supply the module-sheafification definitions used by the statements.

No existing module or declaration is withdrawn. The comparison and induction plans
are retained; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The cited `Functor.kInjective_computes` records comparisons in homotopy categories
and ordinary derived cohomology; its clause (2) does not directly assert the displayed
isomorphism for the canonical unbounded `rightDerivedFunctor`. The already proved
upstream `rightDerivedFunctorObjQIso` gives the required comparison immediately.

The existing `CondensedDerivedInvariants` public import supplies the actual abelian,
Grothendieck, restriction-exactness and derived-category instances used in the Lean
assembly. Its node is now explicitly included in the affected proof steps. This
records a dependency already noted by the stage-2 reviewer; no new infrastructure
or hypothesis was introduced.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
