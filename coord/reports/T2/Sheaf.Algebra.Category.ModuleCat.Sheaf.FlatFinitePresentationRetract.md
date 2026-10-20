## What changed

Proved `SheafOfModules.exists_local_finiteFree_retract_of_flat_of_finitePresentation`
with its original signature. The proof follows Stacks 08FC (finite-relation induction)
and 08FD (descent through a presentation cokernel). It reads a finite presentation
as a coefficient matrix, factors all relations locally by induction, constructs the
finite-free maps, descends through the preserved cokernel, and cancels its epimorphism.
Finally it binds the presentation covering with the factorization covering and identifies
finite free coproducts with finite products. All helpers are private and proved.

Uses the existing independent-universe local relation criterion from
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses`.
Proves colimit preservation for `overMap` directly using Mathlib's cocontinuous
sheaf adjunction and the existing module-sheaf forgetful colimit instance in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
The proof-environment change is recorded in
`coord/changes/flat-finite-retract-proof-environment.md`.
Private coordinate and section morphism constructors are irreducible, with proved
characterizing lemmas, to control elaboration of categorical constructions.
The restriction functor's additivity is proved sectionwise before mapping finite sums.
No public definition or statement changes, consumer adaptations, or new nodes are needed.
The proof is checked by the delivery tool, including its axiom probe. Its public theorem
signature was compared verbatim with the current shared source and is unchanged.
After an intermittent timeout, the scalar-composition evaluation was abstracted over its
target module and `scalarHom` made non-exposed; the revised proof compiled in 46 seconds
under profiling. Two unused private finite-free expansion helpers were removed.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.exists_local_finiteFree_retract_of_flat_of_finitePresentation`
(node `lem-sf-site-flat-fp-finite-retract`). Zero holes added, zero split off,
and no `sorry` remains in the delivery's Lean module. All intermediate helpers
are fully proved. This is a proof, not a decomposition.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the ordinary Grothendieck topology
  sieve covering axioms suffice.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterion`
  (node `lem-weil-pbc-site-flat-equational-criterion`): replaced its small-site
  precoverage criterion by the already proved independent-universe forward criterion
  `lem-weil-pbc-flat-local-relations-universes`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent` and
  `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
  (node `lem-pur-site-restriction-module-adjunction-exact`): the proof needs only
  preservation of colimits along `overMap`, proved directly from existing adjunction
  and forgetful-functor results. No extension-by-zero construction or derived
  adjunction is needed.

The unit's finite-projective-model route is retained. None of its steps is bypassed.
The obsolete top-level `tool_uses` approvals for
`lem-weil-pbc-site-flat-equational-criterion` and
`lem-pur-site-restriction-module-adjunction-exact` are withdrawn in the node copy;
the new `proof_deps` record the criterion and forgetful-colimit result actually used.

## Where the brief, the DAG or earlier work was wrong

The originally imported flatness criterion assumes a small category and a precoverage;
the assigned statement has independent object and morphism universes and an arbitrary
Grothendieck topology. The existing universe-general forward criterion fits exactly.
The earlier saved proof was unvalidated and contained naturality-direction errors,
missing forgetful colimit instances, and expensive unfolding of local constructions.
These are repaired in the assigned module, without changing any public statement or
any definition used by a target. The prior server nonresponses were distinguished from
Lean diagnostics; all compile requests were checked before retrying.

Edge cases: the zero-relation induction uses the identity coefficient matrix on the
top sieve; zero generator ranks use empty finite sums. Binding covering sieves also
allows empty covering families. No sectionwise surjectivity or flatness of section
modules is assumed. The cokernel is used categorically.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
