## What changed

Proved `CategoryTheory.exists_linear_scalarLocalization_category` in
`Sheaf.CategoryTheory.LinearScalarLocalization`, with its existing public signature
and imports unchanged. Private helpers explicitly construct bilinear composition,
prove uniqueness and the category laws, and show that base-changed Hom maps preserve
composition. The main proof constructs the category, both linear structures, the
localization functor, and the extended strict automorphisms. The inverse functor's
linearity follows from Mathlib's equivalence inverse instances.

Repair of return at `9e7b271574`: made all ring, category, instance, and localization
parameters explicit in `LinearScalarConstruction.composition_tmul`, and qualified its
composition as `LinearScalarConstruction.composition`. The private helper evaluates
an explicitly constructed bilinear map. The superficially identical downstream
`ScalarLocalization.composition_tmul` evaluates `ScalarLocalization.composition`,
a different constant defined by choosing the unique map supplied by this module's
existence theorem. Importing that downstream lemma would create an import cycle,
confirmed by `tools/import_direction.py may`. The return explicitly allows stating
the binders when matching texts have different meanings; this repair makes that
distinction explicit, without renaming or duplicating the downstream declaration.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.exists_linear_scalarLocalization_category`
(node `lem-weil-linear-scalar-localization-category`).
Holes closed: 1. Holes added: 0. Sorries left: none. Split-offs: none.
The repair starts from the retained complete proof and adds no holes.
All private helpers are proved. The prescribed single-file compiler passed cleanly
in 6.6 seconds after the repair.

## No longer needed

None. No imports removed, no modules withdrawn, and no DAG nodes bypassed.
All four recorded proof dependencies remain used through their Mathlib declarations:
`def-weil-ring-localization-away`, `def-weil-linear-category`,
`def-weil-module-base-change`, and `def-weil-linear-functor`.
The original five-step route is unchanged, so no node edits are needed.

## Where the brief, the DAG or earlier work was wrong

The prior delivery gave two different composition constants the same unqualified
textual formula. The import-pruning check therefore identified them as the same
statement. Explicit parameters and a qualified constant now disambiguate the
constructive helper from its downstream consumer's chosen map.

No mathematical or public interface correction was needed. Both downstream modules,
`ScalarLocalization` and `ScalarLocalizationTriangulated`, retain the same interface
and need no adaptations. Tensor induction covers empty categories, zero Hom modules,
and the zero localization; no additional nondegeneracy assumptions are used.
The existing helper-section change record is retained and updated:
`coord/changes/linear-scalar-localization-private-proof-helpers.md`.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
