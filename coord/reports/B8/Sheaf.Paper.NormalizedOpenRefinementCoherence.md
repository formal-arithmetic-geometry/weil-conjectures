## What changed

Filled all five original theorem holes in
`lean/Sheaf/Paper/NormalizedOpenRefinementCoherence.lean`, with signatures and definitions
unchanged. Added one proved private restriction-equation helper. The proof uses the
published adjunction Hom equivalence, cancellation of invertible restriction components,
and the identity and composition equations of `IdentityOpenDerivedRestriction`.
Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage`
for existing full faithfulness, which makes the actual underived unit invertible;
`Adjunction.isIso_mapDerivedCategoryAdjunction_unit` then proves the derived-unit assertion.
Validation: the complete delivered module compiled cleanly through `lcompile.py`
in 13.5 seconds, with no errors or warnings.
Updated the existing node's proof route and dependencies accordingly. No interface changes,
new nodes, statement changes, source-library modifications, or consumer adaptations.

## Proved and sorry left

Closed 5 of 5 original holes:
- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_open_refinement_unit_isIso`
- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_open_refinement_coherence`
- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_open_refinement_naturality`
- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_open_refinement_id`
- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_open_refinement_comp`

All realize `lem-sfb-normalized-open-refinement-coherence`. Zero holes remain in the
item, zero holes were added, and zero statements were split off. The proved private
helper is `normalizedOpenRefinement_restrict`. The existing restriction theorems are
used as stated, including their existing proof obligations downstream.

## No longer needed

Removed three proof-only imports:
- `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps`
- `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`

The first two correspond to the unused proof dependencies
`def-sfb-open-closed-internal-hom-comparisons` and
`lem-sfb-condensed-support-derived-localization`; neither complementary closed immersion
nor transport to supportPullback is necessary. Removed the obsolete top-level approval
for the localization tool use. The quasi-isomorphism-resolution helper is not used by
this proof; the existing direct-image comparisons provide the required API.
The identity and composition comparisons remain necessary, so
`lem-sfb-identity-open-derived-restriction` and
`lem-sfb-module-derived-compositor-coherence` remain dependencies.
These are local dependency prunings, not a claim that the removed modules have no other users.

## Where the brief, the DAG or earlier work was wrong

The original first proof step prescribed an unnecessary complementary-support argument.
The already published full faithfulness of open extension by zero and the exact-derived
adjunction instance suffice. No statement is disputed or changed. The unit route and
all four coherence assertions are preserved, with arbitrary unbounded input and no
properness, density, or extra coefficient hypothesis. Edge cases including the empty
open, zero coefficient ring, identity refinement, and identity open require no separate
hypotheses: the proof is entirely in the given categories and uses their adjunctions.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
