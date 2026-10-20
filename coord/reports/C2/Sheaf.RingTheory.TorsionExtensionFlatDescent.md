## What changed

Retired `Sheaf.RingTheory.TorsionExtensionFlatDescent`, as listed in
`coord/retire-items.tsv`, in favor of the already proved upstream module
`WeilConjectures.RingTheory.TorsionExtensionFlatDescent`. Repointed
`lem-weil-pbc-torsion-extension-flat-descent` to its upstream declaration
`LinearMap.exists_torsion_extension_flat_descent`, with the upstream signature.
The signatures differ only in four hypothesis binder names.

The sole DAG parent is already attached to
`WeilConjectures.RingTheory.FormalGlueingEssentialSurjectivity`, which already imports
and applies the upstream replacement. There are no current or quarantined Lean
importers requiring adaptation. The node, its statement, proof dependencies and unit
route are preserved. No upstream source changes.

Validation: compiled the current duplicate, an example of the entire old signature
proved by the upstream theorem, the refreshed upstream replacement and parent
sources, and the empty withdrawal stub individually through lcompile.py. The theorem and parent probes both list exactly `propext`, `Classical.choice`,
and `Quot.sound`. All five compile checks succeed with no warnings. The delivery
checks validate the withdrawal and node record.

Change record: `coord/changes/C2-retire-torsion-extension-flat-descent.md`.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off; zero holes
left in the retiring item. `LinearMap.exists_torsion_extension_flat_descent` remains
available with its existing complete upstream proof. This is duplicate retirement,
not a new proof or a decomposition.

## No longer needed

The duplicate module `Sheaf.RingTheory.TorsionExtensionFlatDescent` is withdrawn.
Its three public Mathlib imports and its four proof imports (cyclic extension descent,
direct-sum extension assembly, torsion cyclic presentation and torsion Hom comparison)
are removed with that duplicate. These mathematical dependencies remain used by the
upstream proof; no dependency node is withdrawn. In particular, the upstream theorem
and its parent's declarations are preserved in full.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module containing a hole. The current item has
zero holes and is explicitly a retirement item. Its old Lean attachment still named
the duplicate after the parent migrated upstream. The reviewed delivery `afd4aa3de` was not merged because B4's landing
`f550737119` changed the duplicate's cyclic-descent import after the delivery base
`894c53ba6`. Rechecked the current duplicate with that upstream cyclic-descent import,
then reapplied its retirement. The delivery tool constructs the replacement commit
on freshly fetched `sheaf-dag`; no intervening source edit is reverted.

Refreshed both upstream source probes from the current shared repository and
recompiled the current duplicate, replacement, parent, old-signature application,
and empty withdrawn-module stub through the server compile tool. The current
source uses upstream modules for all four proof imports.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
