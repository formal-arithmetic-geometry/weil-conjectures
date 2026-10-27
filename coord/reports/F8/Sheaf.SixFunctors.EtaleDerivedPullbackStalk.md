## What changed

Proved `AlgebraicGeometry.Etale.exists_etaleDerivedPullbackStalkIso` in
`Sheaf.SixFunctors.EtaleDerivedPullbackStalk`, with its original statement unchanged.
Use the existing `upperStarCompSheafFiberIso` for `ModuleCat A`, apply it termwise,
and descend directly with `Localization.liftNatIso`. Whiskered exact-derived
factorizations give the specified normalization on every representing complex.
Updated the declaration's proof explanation and the existing node's proof,
proof dependencies and proof origin to describe this construction. No definitions,
public imports or other modules changed. No new statements or nodes.

The generic site-level comparison realizes `lemma-openclosed-stalk-upperstar`;
it is used solely as a stalk comparison tool, with the preservation unit's route
unchanged. The comparison is already module-valued, so linearity is part of its
morphisms. Existing Mathlib exactness and additivity instances suffice. Server
compilation passed after removing the three unused private imports.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.exists_etaleDerivedPullbackStalkIso`
(node `lem-sf-etale-derived-pullback-stalk`).

Holes closed: 1. Holes added: 0. Holes left in delivered Lean: 0.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
No split-off statements. The proof uses the existing functor constructions and
localization API rather than any additional unfinished theorem.

## No longer needed

Removed these private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `Sheaf.CategoryTheory.ExactDerivedComposition`

The revised proof does not use these former planned proof dependencies:

- `prop-weil-pbc-inverse-image-modules-exact`: the statement already uses
  module-category-valued inverse image; its exactness instances suffice. Retained
  its statement dependency, since that field records the mathematical interface.
- `lem-weil-pbc-inverse-image-stalk-germ`: the germ normalization is not needed;
  the generic module-valued `upperStarCompSheafFiberIso` is exactly the comparison
  appearing in the theorem's conclusion.
- `lem-sfb-etale-stalk-constant-complex-exactness`, module
  `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness`: no constant-complex
  retraction or scalar-action reconstruction is needed; ordinary point-fiber
  exactness is already available.
- `lem-sfb-exact-derived-composition`, module
  `Sheaf.CategoryTheory.ExactDerivedComposition`: directly whiskering the two
  factorization isomorphisms supplies the necessary normalization, so there is
  no need to construct and then cancel a separate derived composition isomorphism.

These are pruned from this proof, not declarations withdrawn from the library.
The existing public imports are preserved for consumers.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of scalar linearity through abelian sheaves and the
extra normalized derived composition isomorphism are unnecessary. The source
library already provides the canonical comparison for any suitable coefficient
category, including `ModuleCat A`. Direct localization proves the complete
statement and representative equation without these intermediate steps.
No false statement or definition repair was needed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
