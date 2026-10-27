## What changed

Proved `CategoryTheory.RingedHomRestriction.composite_normalized` in
`Sheaf.Algebra.Homology.RingedHomRestrictionComposition`, preserving its statement
and imports. A private categorical pasting lemma composes the two representative
equations using naturality. The main proof applies it to the canonical
augmentations and localization factorizations. The existing composition and
natural-isomorphism factorization lemmas give the required transport equation.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.RingedHomRestriction.composite_normalized`
(node `lem-ringed-hom-restriction-composition-normalization`).
No holes added; no `sorry` remains in the item or its private helpers.

## No longer needed

None. No imports removed and no declared dependency pruned. Both original proof
dependencies remain used: the augmentation/normalization interface of
`lem-ringed-hom-restriction-comparison-descent` and the derived internal Hom
functor of `def-pur-derived-internal-hom`. No new proof imports are required.

## Where the brief, the DAG or earlier work was wrong

None. The proof implements the existing two-step plan without changing the
statement, definitions, source declarations or unit route.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
