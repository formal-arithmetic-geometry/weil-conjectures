## What changed

Proved all 15 law theorems in `Sheaf.CategoryTheory.FilteredTwoColimitModel`, following
all three paragraphs of the current blueprint model proof: filtered Hom diagrams,
composition, and the comparison functor. Existing public statements, definitions,
instances, visibility, and public imports are unchanged.

Added five proved private helpers for normalized transport, transport of products,
transport of composite representatives, composition at one stage, and comparison
invariance under transition. These implement elementary steps already in the model
node's proof. No new mathematical dependency or public declaration is introduced.

Replaced the proof import `Mathlib.CategoryTheory.Limits.Types.Filtered` with
`Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered`. The Hom colimit universal
property is proved by quotient descent, and its equality criterion uses
`Functor.ιColimitType_eq_iff_of_isFiltered` directly. Composition and comparison
respect the generating transition relations, so their descent needs no appeal to
the full eventual-equality criterion. Updated the existing node's proof accordingly.

Change record: `coord/changes/filtered-two-colimit-model-private-helpers.md`.
Preflight requests it for the scoped `omit` commands on three private helpers;
public interfaces remain unchanged. The sole direct importer,
`Sheaf.CategoryTheory.FilteredTwoColimitCharacterization` (unclaimed), needs no edit.

The completed module compiles on the project server. Checked `#print axioms` for
`category`, `comparison`, `homCocone_isColimit`, and `homClass_eq_iff`: each lists only
`propext`, `Classical.choice`, and `Quot.sound`.

Searches with msearch Lean Finder and Loogle, plus local Mathlib/library searches,
found Mathlib's ColimitType API. Grothendieck constructions do not provide this
model's eventual Hom classes; no alternative project construction was needed.

## Proved and sorry left

Closed 15 holes, all attached to `det-def-sfb-filtered-two-colimit-model`.
The following names are in namespace `CategoryTheory.FilteredTwoColimit`:

- `homTransition_id`
- `homTransition_comp`
- `homClass_transition`
- `homCocone_isColimit`
- `commonStage_isFiltered`
- `homClass_eq_iff`
- `compRepresentative_eq_compAt`
- `compRepresentative_rel_right`
- `compRepresentative_rel_left`
- `identity_comp`
- `comp_identity`
- `comp_assoc`
- `mapHomRepresentative_rel`
- `mapHom_identity`
- `mapHom_comp`

Remaining holes: none. Added holes: none. Split-off statements: none.
The category and comparison functor consequently have no sorry dependency.

## No longer needed

Removed the proof import `Mathlib.CategoryTheory.Limits.Types.Filtered`, using
`Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered` for the concrete quotient
criterion instead. No project modules or DAG nodes are pruned: the cocone,
category-colimit, and filtered-set-colimit dependencies remain needed.

The full filtered-set equality criterion is unnecessary in the representative
independence and comparison descent steps, which use the generating relation.
It remains needed for `homClass_eq_iff`; the node's overall dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The unit route is retained. The existing docstring
for `homClass_eq_iff` describes passing through the ULift cocone's universal
property; Mathlib proves the same criterion directly for the concrete ColimitType.
This avoids that extra comparison, while `homCocone_isColimit` is proved as required.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
