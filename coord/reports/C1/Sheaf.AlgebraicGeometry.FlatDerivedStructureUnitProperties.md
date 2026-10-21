## What changed

Restored `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties` from the exact
quarantine path in `coord/rework.tsv`. The sole source edit replaces
`public import Sheaf.AlgebraicGeometry.DerivedPullback` with
`public import WeilConjectures.AlgebraicGeometry.DerivedPullback`.
The former is an empty withdrawn module; the latter supplies the public declaration
used in the theorem's signature. The original theorem, private field helper,
docstrings, and both proof branches are byte-for-byte preserved.

`AlgebraicGeometry.flat_derived_structure_unit_properties` proves negative fibre
vanishing by the canonical flat base-change isomorphism and nonnegativity of right
derived direct image. Its degree-zero assertion uses the canonical structure-map
base-change equation, the degree-zero direct-image unit equation, and the private
calculation detecting the ordinary structure map over a field on the empty and
whole opens. The canonical compatibility dependency is now proved in the library;
no additional theorem or split is needed.

The repaired module compiled cleanly through `lcompile.py` in 20 seconds, and again
in 15 seconds during the consumer check. Updated only the item's `lean.note` in its
DAG record; the attachment, statement, proof and all dependencies are preserved.
The change record is
`coord/changes/C1-flat-derived-structure-unit-properties-restoration.md`.

## Proved and sorry left

This is a zero-hole quarantine restoration, not a newly closed proof hole.
The archived source has zero `sorry`, and the restored module has zero `sorry`.
Holes closed: zero. Holes added: zero. Split-off statements: zero.

The restored public theorem is
`AlgebraicGeometry.flat_derived_structure_unit_properties`
(node `flat-derived-structure-unit-properties`). Its existing private helper
`isIso_structureMap_over_field` is fully proved as well.
No declaration with an unfinished proof is delivered.

## No longer needed

Removed the empty compatibility import `Sheaf.AlgebraicGeometry.DerivedPullback`,
replacing it with the adopted source implementation that the unchanged statement
requires. This is an import migration; no mathematical dependency, node, theorem,
or module is withdrawn or claimed globally pruned.

The existing node proof still uses all five recorded proof dependencies. The
unit `sk-prop-av-cube` and its realized route are unchanged. The quarantined parent
`Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit` still cites and needs this item.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined, not because its theorem
is unused or withdrawn. The archived proof is already complete. Its only current
source incompatibility is the public import of the now-empty derived-pullback
compatibility module: without the migration Lean reports `derivedPullback` as
privately imported in the public theorem signature.

Library searches through `msearch.py` (LeanFinder, Loogle, and grep) and local source
searches found no replacement fibre theorem. The source single-pullback comparison,
flat-invertible base-change result, right-derived nonnegativity, H0 normalization,
and proved canonical structure-map equation supply the existing proof unchanged.

There are no live Lean consumers of this quarantined module. Its quarantined parent
was checked against the restored module with `lcompile.py --all`: the parent itself
still publicly imports the empty Sheaf derived-pullback module and fails at its own
public signature with the same `derivedPullback` visibility error. That separate
quarantine restoration is not caused by a changed theorem signature here. A scratch
check with its public import migrated to the adopted source compiled in 9 seconds;
no parent source or other group's module is included in this delivery.

The completed `downstream.py --allow-missing --uses` scan reports zero live downstream
modules and zero live uses of the theorem. The scratch consumer copy is outside
`lean/` and is excluded from delivery.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
