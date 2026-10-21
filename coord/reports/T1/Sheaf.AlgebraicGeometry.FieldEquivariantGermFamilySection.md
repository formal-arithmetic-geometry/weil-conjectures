## What changed

Completed the zero-hole retirement listed in coord/retire-items.tsv. Withdraw
Sheaf.AlgebraicGeometry.FieldEquivariantGermFamilySection and attach its node to
WeilConjectures.AlgebraicGeometry.FieldEquivariantGermFamilySection. Adapt the sole
direct consumer, Sheaf.AlgebraicGeometry.GaloisStalkActionFull, by migrating its
private import and transporting its local section construction through ULift.
The public signature and visibility remain identical. Both nodes record the route.
Change record: coord/changes/T1-retire-field-equivariant-germ-family-section.md.

Loogle located presheafFiberCompIso and its germ comparison. Leanfinder found no
exact reconstruction theorem; msearch grep and local source search confirmed the
complete adopted theorem. Read both the source theorem and its one-point dependency,
and the local Stacks source Tags 04JM and 03QW. The import-cycle check passes.

## Proved and sorry left

Initial holes: zero. Holes closed: zero. Holes added: zero. No sorries remain in
the delivered consumer. The source declaration
AlgebraicGeometry.Scheme.field_equivariant_germ_family_section retains its complete
proof. This is duplicate retirement, not a hole closure or decomposition.
No result is split off. The adapted consumer compiles cleanly with lcompile.py
in 4.6 seconds; delivery checks additionally verify axioms.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.FieldEquivariantGermFamilySection.
Remove its sole private consumer import, replacing it with the adopted source.
The duplicate private section_germ_ext_of_lifts helper and singleton-cover proof
are no longer duplicated locally; their complete source versions remain intact.
No mathematical dependency node is pruned: the germ-family node and its one-point
dependency remain needed, with their adopted source declarations. No source-library
module or declaration is deleted or changed. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof item, but the current queue marks this item
as retire and its current module has zero holes. The adopted theorem uses
max (u + 1) v, whereas the consumer requires max u v. An import swap alone fails
with max (u + 1) v =?= max u v at the local-section application. Explicit ULift
transport is therefore necessary and is now implemented. All field hypotheses,
the canonical action formula, covariance, and the public consumer type stay fixed.
Empty etale objects retain the adopted theorem's empty-cover argument. ULift and
the stalk equivalence introduce no nonemptiness hypothesis and also handle empty
section types. The mathematical statement and unit route are unchanged.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
