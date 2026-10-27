## What changed

Restored `Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories` from its
`coord/rework.tsv` quarantine source. Replaced the public import of the withdrawn empty
`Sheaf.AlgebraicGeometry.DerivedPullback` with the current defining module
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. This fixes the recorded private-import
failure without changing any declaration signature or proof.

Change record: `coord/changes/F4-diagonal-local-derived-pullback-import.md`.

The existing proof uses `nonempty_derivedPullback_structureSheaf_iso` to lift the structure
sheaf comparison to the quasi-coherent full subcategory, applies
`proper_flat_selfProduct_rightAdjoint_baseChange_local` at the degree-zero structure sheaf,
and composes with the inverse image of the lifted comparison under `b`. Both dependencies
and the item's node `lem-sc-diagonal-basechange-local-derived-categories` are preserved.
The local-localization theorem is needed: the related `diagonal_baseChange_upperShriek`
instead requires a family of derived localizations for every scheme.

Consumer check: there are zero current Lean importers. The quarantined
`DiagonalPushforwardStructure` still imports this module and calls the unchanged theorem;
its dependency is preserved. No archived file is deleted or replaced by an empty module.

Validation: the restored module compiled through `lcompile.py` in 5.6 seconds, exit 0,
with no warnings. The only difference from the archive is the public import replacement.

## Proved and sorry left

`AlgebraicGeometry.diagonal_baseChange_upperShriek_local` already has a complete proof in
the archive. This is an assigned import/restoration repair with 0 original holes, 0 holes
closed, 0 holes added, and 0 remaining holes in the restored module. No new theorem, axiom,
definition, or split-off obligation is introduced.

## No longer needed

The obsolete public import `Sheaf.AlgebraicGeometry.DerivedPullback` is replaced by its
upstream defining module. That withdrawn module contains no declarations. No mathematical
dependency, node, or module is pruned: both proof dependencies remain used, and the unit
route and archived parent dependency are retained. The other imports remain as in the
archive because they supply the public statement or its two proof dependencies.

## Where the brief, the DAG or earlier work was wrong

This item is the zero-hole rework listed in `coord/rework.tsv`, not an outstanding proof
split. The quarantine error is caused by the obsolete public import after migration of
`derivedPullback`; neither the theorem nor its proof plan requires correction. Mathlib
LeanFinder and Loogle searches found ordinary pullback adjunctions and `ObjectProperty.isoMk`,
not a shorter substitute for the local derived base-change theorem. Source searches found
the two recorded dependencies already in their current modules. No DAG field changes are
needed because the restored declaration and argument are identical to the existing record.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
