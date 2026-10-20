## What changed

Retired the duplicate `Sheaf.CategoryTheory.NaturalTruncationCouple` through
`deleted.txt` and reattached `lem-pc-natural-bounded-below-truncation-couples`
to `WeilConjectures.CategoryTheory.NaturalTruncationCouple`. The public theorem
signature is byte-identical. The adopted proof explicitly constructs the raw
couple, transfers lower bounds from bounded-below representatives, and proves
both natural comparison equations using raw truncation naturality.

The current coproduct consumer already imports the adopted module. Its proof
and every adopted-source file remain unchanged. Server checks compile the
adopted module, the current coproduct consumer, and a separate application of
the adopted theorem to the duplicate's exact signature. Axiom probes contain
only the three permitted axioms. The adopted import closure contains no Sheaf
module or duplicate twin pair.

Change record: `coord/changes/U3-retire-natural-truncation-couple.md`.

## Proved and sorry left

Zero holes before; zero holes left; zero holes closed; zero holes added;
zero split off. This completes a listed retirement, not a new proof.
`CategoryTheory.exists_natural_boundedBelow_truncation_couples` remains proved
by the adopted module with exactly its original signature. The private helpers
`zero_projection_square`, `rawCouple`, and `abutmentMap_isIso` are already
implemented there. No declaration with `sorry` remains or is introduced.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.NaturalTruncationCouple`.
Its duplicated implementation and private helpers are no longer needed.
There are no remaining consumer import lines to replace. No mathematical node
or proof dependency is removed: the existing natural-couple node and all its
dependencies remain in the DAG, with its Lean attachment moved to the adopted
module. The coproduct parent continues to use that same node and theorem.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes or a repair. The current
queue and `coord/retire-items.tsv` identify this item specifically as a
zero-hole retirement. The row lists a former Sheaf coproduct consumer and
prerequisite modules from its snapshot; the prerequisites and consumer have
already been retired. Current source and DAG searches, including quarantined
files, find no remaining importer of the duplicate. The sole DAG parent already
has the adopted attachment and imports the replacement. The node's old Lean
attachment was stale; its mathematical statement and four-step proof are valid.
No target, definition, statement, or unit route is changed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
