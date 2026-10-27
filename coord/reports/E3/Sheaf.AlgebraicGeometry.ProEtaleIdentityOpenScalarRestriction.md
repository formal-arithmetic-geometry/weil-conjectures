## What changed

Proved `AlgebraicGeometry.Scheme.sfIdentityOpenRestriction` in the assigned module, with its
statement unchanged. Private proved helpers identify identity restriction in fixed coefficients,
transport its normalization and coefficient square through the realization equivalences, and
compare the ordinary sheaf maps using the open adjunction Hom equivalence. The existing
`Functor.mapDerivedCategorySquareIso_hom_app_id` then lifts the equality to the entire unbounded
derived category. Added its source module as a private proof import. Both public imports stay.

Updated the item node's proof, proof dependencies, and proof origin to describe this argument.
The unit `sk-input-weights` has no realized nodes or steps; its route is unchanged.
No existing definition, declaration signature, global instance, or global attribute changes.
The final single-file server compile passed without errors or warnings in 27.9 seconds;
static checks also confirm the original theorem signature and both public imports are unchanged.

The proof-environment commands are documented in
`coord/changes/E3-identity-open-scalar-proof-environment.md`. There are no direct Lean importers
of the item, as checked with `tools/downstream.py` and direct-import searches. Unfinished DAG
parents retain the unchanged statement and attachment.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.sfIdentityOpenRestriction`
(node `lem-weil-identity-open-scalar-restriction`). Added 0 holes. No `sorry` remains in the item
or in any newly added module; no new module is added. This is a proof, not a decomposition.
Existing dependency proofs, including the realization normalization, are used through their
published declarations; their independent obligations are unchanged.

## No longer needed

Removed the direct proof dependency `def-weil-presheaf-modules-sheafification` from the item
node. Its universal-property calculation is already packaged by the published adjunction and
normalized scalar-comparison API, so it is not reimplemented here. This does not withdraw that
node or claim its module leaves the targets' transitive closure.
No existing imports were removed, and no module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The existing statement is correct. The former plan's final degreewise/localization step has an
existing proved implementation, `Functor.mapDerivedCategorySquareIso_hom_app_id`. The sheaf
calculation must also identify the normalization defined using abstract pullback with the
normalization defined using sectionwise open restriction; the private fixedRestrictionId and
fixedUpperStarId calculations make that identification explicit. No statement repair is needed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
