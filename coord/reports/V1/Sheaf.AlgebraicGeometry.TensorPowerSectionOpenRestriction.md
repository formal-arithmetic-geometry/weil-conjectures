## What changed

Retired `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` via `deleted.txt`.
Reattached `lem-sc-tensor-power-section-open-restriction` to the existing proved
`AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_open_restriction` in
`WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestriction`.

The upstream signature has an anonymous image-equality binder where the copy names
it `hW`; every hypothesis and conclusion agrees. A scratch example with the complete
original signature compiles by exact application of the upstream theorem. The actual
consumer `WeilConjectures.AlgebraicGeometry.AffineOpenSectionFractionLocalization`
compiles unchanged (11.2 seconds) and already imports the upstream theorem. No upstream
file, target statement, definition, declaration signature, attribute, or public import
was edited.

Change record: `coord/changes/retire-tensor-power-section-open-restriction.md`.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: 0. Holes added: 0.
No remaining or split-off sorry declarations. No new mathematical proof is claimed.
The retained upstream theorem's `#print axioms` lists exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

The duplicate module `Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction` and
its private helper `openRestrictionNumeratorIso_inv_tmul` are withdrawn. Its three
imports disappear with it: the public import of
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators` and the proof imports
`WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN` and
`WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionT`.
These upstream modules remain needed by the upstream theorem; none is removed or
claimed globally pruned. The mathematical node and all its proof dependencies stay:
only its Lean attachment changes, preserving the unit's argument.

A full source search finds zero current importers of the retired Sheaf module. The
sole external theorem-name use is the upstream affine-localization consumer, which
already selects the retained upstream implementation. No additional nodes or modules
are pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief refers to sorry obligations, but the queue assigns this item
as `retire`, with zero holes. The retirement inventory's listed Sheaf affine-localization
consumer has already disappeared from the current tree; its upstream counterpart
already imports the upstream restriction theorem. Consequently there are no consumer
adaptations to deliver. The old DAG attachment still selected the now-redundant copy;
this packet corrects that attachment without changing the mathematical statement.

Searches were actually run through `msearch.py`: LeanFinder returned eight related
Mathlib restriction/localization results; Loogle returned twelve `restrictAppIso`
results; its grep service returned zero hits for the full theorem name. Direct `rg`
search of both source roots found the exact upstream duplicate and its sole consumer.
No new nodes or retained obligations were introduced.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
