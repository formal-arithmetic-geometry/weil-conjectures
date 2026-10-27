## What changed

Proved `CommRingCat.isSepClosed_of_isColimit` in
`Sheaf.FieldTheory.SeparablyClosedFieldColimit` without changing its signature.
Only finitely many polynomial coefficients descend. The field-map theorem
`Polynomial.separable_map` reflects separability to the stage; separable closedness
there gives a splitting, and `Polynomial.Splits.map` transports it to the colimit.
Updated the proof docstring and the item's DAG proof to match this argument.

Replaced the private proof import `Sheaf.RingTheory.FilteredColimitFiniteData` with
`Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Mathlib.Algebra.Polynomial.Eval.Subring`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.Data.Finset.Order`. Existing public imports are preserved.

The new dependency `lem-pc-filtered-colimit-commrings-elementwise` is a Mathlib
leaf used only for its generic representative-existence clause. It replaces the
heavier generic finite-data descent tool, without bypassing any blueprint unit.
The item's unit record has no realized statement or steps attached to this node.

## Proved and sorry left

Closed the one original hole: `CommRingCat.isSepClosed_of_isColimit`
(node `lem-sfb-separably-closed-field-colimit`). Added zero holes; split off zero
statements. No `sorry` remains in any delivered Lean file.

Validation: the final Lean file compiled cleanly through `lcompile.py` in 3.3 s
(exit code 0), within the 60 s limit.

Edge cases: empty support chooses an upper stage using nonemptiness and represents
all coefficients by zero; constants also lift. Separability reflection applies
in every characteristic and requires no algebraicity of stage extensions.

## No longer needed

Removed proof import `Sheaf.RingTheory.FilteredColimitFiniteData` and the direct
proof dependency `lemma-nagata-filtered-colimit-finite-data`: coefficient lifts
suffice because all stages are fields, so separability reflects along their maps.
Removed its obsolete `tool_uses` entry. The lemma and module remain available to
other consumers; this delivery does not withdraw them.

Removed direct proof dependency `def-weil-polynomial-root`: the proof transports
splittings instead of roots and needs no finite-sum evaluation argument.
No existing declarations or modules are withdrawn. No new modules are added.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The earlier plan was unnecessarily strong: it descended
both coefficients and a Bezout identity, although Mathlib already reflects
separability along any map from a field. The shorter proof preserves the same
statement and the unit route. No shared definitions or interfaces changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
