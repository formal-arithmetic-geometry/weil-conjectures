## What changed

Proved `AlgebraicGeometry.Scheme.normalizedImmersionComparisonCoherence` in
`Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence`. Its theorem signature,
all supplied data, the comparison composite, and every mathematical equation are preserved.
Added private proof imports of `NormalizedComparisonBinaryRestriction`,
`NormalizedComparisonTowerRestriction`, `ExactRestrictionComposition`,
`MapDerivedCategoryCocycle`, and `MapDerivedCategoryMate` from their existing Sheaf/WeilConjectures modules.

Repair of the return at head `10e302c7e`: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.derived_identity_factors`. The existing public theorem
`CategoryTheory.Functor.mapDerivedCategoryIdIso_hom_app_Q_obj` from
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition` supplies the
identity-factorization equation directly in `derived_restriction_eq`. The duplicate
identified by the return, `AlgebraicGeometry.Scheme.identity_factors`, is private to
`LocallyClosedExtensionCoherence`; the public theorem has the same explicit binders and
conclusion and avoids changing that module or its visibility.

Private proved helpers identify the supplied derived restriction and compositor using their
termwise characterizations, descend the module normalization by exact-functor composition
coherence, and transport it along the cartesian coefficient equality. The restriction Hom
bijection detects equality after conjugating the source into the extension image.
Closed–open factorization supplies a normalized comparison, whose proved uniqueness
justifies choosing it. Binary normalization gives both factorization orders and composition.
The tower-restriction theorem and the same Hom detection give the tower equation.
All three original proof dependencies remain used; the unit's route is preserved.

To resolve a kernel definitional-equality bottleneck, factored the two existing equations
into the fully defined predicates `CategoryTheory.immersionComparisonNormalized` and
`CategoryTheory.immersionComparisonComposition`, each in its own new public module.
`Functors.Normalized` and the composition clause of `Functors` now use them with exactly
the original arguments and quantifiers. Their unfoldings are the original equations.
The change record `coord/changes/Z9-normalized-immersion-comparison-predicates.md` includes
both original and replacement definitions and the consumer audit. The item publicly imports
the new modules because the public definition bodies use them. No source-library module
is changed. Local proof elaboration settings are documented in the same record.

Validation of the returned-packet repair: all three delivered Lean modules compiled
without warnings. The definition modules took 1.2 and 1.1 seconds, and the repaired item
took 23.8 seconds. The import-direction check confirms that the added private proof import
creates no cycle. Source checks find zero `sorry` tokens and no Lean line over 100 characters.
The retained delivery previously compiled the sole downstream importer unchanged in
59.2 seconds; this repair changes only private proof code and adds a private proof import.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.normalizedImmersionComparisonCoherence`
(node `lem-sfb-normalized-immersion-comparison-coherence`).

Holes closed: 1. Holes added: 0. Sorries left in the item: 0. No statements were split off.
The two new modules contain genuine definitions, not pending theorems; both have zero holes.
Every private helper is proved. Imported dependencies retain their existing proof status;
this delivery does not claim that their transitive import closure is axiom-free.

## No longer needed

The copied private helper `derived_identity_factors` is no longer needed; its sole use
now applies the existing public theorem directly. No imports were removed, and all three original proof dependencies are used:
`lem-sfb-locally-closed-extension-coherence`,
`lem-sfb-normalized-comparison-binary-restriction`, and
`lem-sfb-normalized-comparison-tower-restriction`.
No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated the identity-factorization theorem, even though a public
version already exists in `ExactRestrictionComposition`; this repair reuses it.
No mathematical discrepancy was found. Derived normalization is not itself a field of
`DerivedCoherence`; it follows from the module extension normalization, the supplied
termwise characterizations, and exact-functor composition coherence. This bridge is proved
privately without changing either coherence structure. The two existing expanded predicates
were expensive for Lean's kernel at the scheme specialization; naming their unchanged
equations over arbitrary categories removes that repeated unfolding.

## New nodes

`def-sfb-immersion-comparison-normalized` records the existing equation (N) as a predicate
over four arbitrary categories, implemented in
`lean/Sheaf/CategoryTheory/ImmersionComparisonNormalized.lean`. It contains no assertion of
existence or coherence beyond that equation. In empty categories the universal condition
is vacuous, and with identity functors and identity counits it reduces to the specified
comparison equation; there is no extra faithfulness or support assumption.

`def-sfb-immersion-comparison-composition` records the existing q-composition equation over
six arbitrary categories, implemented in
`lean/Sheaf/CategoryTheory/ImmersionComparisonComposition.lean`. Identity and empty-category
cases are included without extra assumptions. Neither definition selects any data, and
neither is a reformulation of the theorem as a new hole. Three kinds of Mathlib search and
a whole-blueprint search found no existing predicate with these exact parameters.

Change record: `coord/changes/Z9-normalized-immersion-comparison-predicates.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
