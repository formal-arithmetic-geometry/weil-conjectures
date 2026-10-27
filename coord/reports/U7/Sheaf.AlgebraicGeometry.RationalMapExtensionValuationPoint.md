## What changed

Proved `AlgebraicGeometry.exists_extension_at_valuation_stalk` in
`Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint`, preserving its statement.
The proof follows Stacks Tag 0BX7 (`morphisms-lemma-extend-across`), in the stated
integral Noetherian case: restrict to the function field, use the valuative criterion
for a lift over the valuation stalk, spread the lift, compare both maps on each
intersection using relative separatedness, and glue the two-member open cover.
The cover's uniqueness proves that the glued morphism is over the original base.

All ingredients are proved Mathlib declarations. In particular,
`Scheme.SpecMap_stalkSpecializes_fromSpecStalk` supplies the canonical-map identity,
`spread_out_of_isGermInjective'` supplies the neighbourhood, and
`ext_of_isDominant_of_isSeparated` proves overlap agreement. Dominance is proved
by the image containing the generic point and cancellation of an open immersion.
`Scheme.Cover.glueMorphisms`, its restriction lemma and `hom_ext` finish the proof.
No declarations or definitions were added. All existing public imports are preserved.

Single-file validation through `lcompile.py` passed in 4.8 seconds with no warnings.
The delivery preflight performs the declaration axiom check.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.exists_extension_at_valuation_stalk`
(node `lem-sfb-rational-map-extension-valuation-point`).

Proved 1 of 1 existing holes; zero holes remain; zero holes were added or split off.

## No longer needed

Removed the private proof import
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`.
Its extra flatness and module-stalk results are unnecessary: the canonical local
scheme morphism, its closed-point formula, its factor through an open, and its
compatibility with specialization are available directly from Mathlib's stalk API.
This avoids the wrapper module and its proof dependencies for this proof.
No upstream declaration is changed or removed. No new dependency modules are imported.

No DAG nodes are withdrawn: the proof realizes all five planned steps, including
the canonical-local-morphism identities of the existing dependency node through
Mathlib's already proved API. No unit statement or unit route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or the five-step plan.
The source-library wrapper import was stronger than the canonical-map API required.
The proof requires relative separatedness only, and never assumes absolute
separatedness of the target or any field structure on the base.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
