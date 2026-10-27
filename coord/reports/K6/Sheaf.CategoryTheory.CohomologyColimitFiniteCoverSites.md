## What changed

Filled `CategoryTheory.cohomology_colimit_of_finite_cover_sites` with the
filtered-abelian-group argument from the node: stage existence gives surjectivity;
a representative of a kernel element is killed after a transition, giving
injectivity; `ConcreteCategory.isIso_iff_bijective` finishes.

The named helper declarations have unrestricted covering axioms and cannot be
applied to this finite-index theorem. Added the finite-index versions in
`Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSitesClassDescent` and
`Sheaf.CategoryTheory.CohomologyColimitFiniteCoverSitesEventualVanishing`.
Reattached the existing two helper nodes to those declarations instead of making
duplicate nodes. Their natural-language statements already concern finite covers.
The source argument, including the degree-zero and dimension-shifting cases,
is recorded in full in each new theorem docstring and its node proof.

This is a decomposition of the assigned hole, not an unconditional proof of
continuity. The existing statement, universes, binders and public imports of the
assigned module are preserved. No other existing Lean module is changed.
The unit route is preserved; no unit statement or realized step is bypassed.

Change record: `coord/changes/finite-cover-cohomology-helper-attachments.md`.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.cohomology_colimit_of_finite_cover_sites`
(node `lem-weil-pbc-cohomology-colimit-of-sites`).

Added 2 whole-theorem holes:

- `CategoryTheory.cohomology_colimit_finite_cover_sites_class_descent`,
  node `lem-weil-pbc-colimit-sites-class-descent`.
- `CategoryTheory.cohomology_colimit_finite_cover_sites_eventual_vanishing`,
  node `lem-weil-pbc-colimit-sites-eventual-vanishing`.

No holes remain in the assigned module. The delivery has two holes in total,
net holes closed minus added = -1. Each helper is strictly one half of the
argument: existence says nothing about relations, and eventual zero says
nothing about existence. Neither alone asserts the assigned isomorphism.
No data is selected from an unproved existence theorem to define an object.

Edge cases checked mathematically: degree zero uses the unit clauses and the
finite-cover section comparison; zero coefficient systems are immediate; a
constant site system gives the ordinary finite-cover continuity statement;
empty covering families force the sheaf condition at their target and do not
need a nonempty-cover assumption. `Under i` is filtered even when the index is
not a poset; transitions, not merely inequalities, are used in the proof.

## No longer needed

Removed the private imports of
`Sheaf.CategoryTheory.CohomologyColimitSitesClassDescent` and
`Sheaf.CategoryTheory.CohomologyColimitSitesEventualVanishing` from the item.
They have been replaced by finite-index helper imports. Their nodes remain
needed, with corrected Lean attachments. Their old declarations and modules
remain in the library, since the unrestricted theorem and its corrected-lift
argument still use them. No module is withdrawn or claimed globally pruned.
All other imports are used by the statement or the concrete colimit proof.
The existing source proof-dependency plan is retained, so no mathematical
subdependency or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The item's proof plan names helper nodes whose previous Lean attachments carry
strictly stronger hypotheses: unrestricted indexed composition and base change.
Finite `R.uncurry` does not imply finite index sets for every presentation of R.
Thus the old proof cannot simply be reused by asking typeclass inference for
those stronger instances. The natural-language helper statements and source
09YP do already cover the finite-index situation, so those statements need no
weakening or repair. Reattaching their nodes records the missing generalization
honestly while leaving the old proved special cases intact.

All three files compiled successfully in dependency order: class descent
30.5 s, eventual vanishing 29.6 s, and the assigned theorem 28.9 s.
The axiom/hole probes are additionally checked by the delivery tool.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
