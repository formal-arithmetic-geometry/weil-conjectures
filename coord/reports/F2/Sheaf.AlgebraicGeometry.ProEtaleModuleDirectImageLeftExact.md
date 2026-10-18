## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage_additive_leftExact`
in the assigned module, with its exact signature and public imports unchanged.
Addition is checked on sections. After forgetting module structures, the direct image
is definitionally the composite of forgetting on the source and continuous pushforward
of abelian sheaves. Both preserve finite limits; the target forgetful functor reflects
finite limits, giving the result. This is the sectionwise-limit proof of Stacks 03DA/03DC
implemented using Mathlib's existing limit API, without constructing an adjunction.
Updated the item's DAG proof, proof dependencies, and proof origin to match.

Removed two redundant private imports. No statement, definition, public visibility, or
other module changed; no change record or consumer adaptation is necessary.

Validation: the proof compiled remotely in 4.3 seconds, and compiled again after import
pruning in 4.4 seconds. `#print axioms` reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. The diagnostic command was removed from the delivered source.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage_additive_leftExact`
(node `lem-weil-proetale-module-direct-image-left-exact`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No intermediate statements or split-offs were added.

## No longer needed

Removed the private imports `Sheaf.CategoryTheory.RingedSiteModules` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
They were redundant direct imports, already available through the unchanged public
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage` import. No global module withdrawal
or reduction in the transitive import closure is claimed.

Removed `def-weil-sheaf-of-modules-category` from the item's proof dependencies:
its `CategoryTheory.ringedSiteModules` alias is unused. The proof uses Mathlib's
`SheafOfModules` and its proved limit API directly. The direct-image definition node
`def-weil-proetale-module-direct-image` remains needed. All planned sectionwise kernel,
zero-object, and exact-sequence glue is supplied by the stronger finite-limit API;
no new obligation is needed for those steps. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original DAG's componentwise
argument is valid; the existing finite-limit API gives a shorter implementation of it.
The result holds for arbitrary commutative coefficient rings, without a finiteness or
geometric hypothesis. Existing source/target universes and all target signatures remain
unchanged. The proof adds no dependence on any unproved declaration.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
