## What changed

Withdrew the declaration-free compatibility module
`Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore` as explicitly
requested by its current `retire` queue row and the retire inventory.
The canonical theorem
`AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom_core` remains in
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore`,
with its complete proof and all upstream source unchanged.
Updated only the explanatory note in the existing node's Lean attachment.
Change record: `coord/changes/R4-retire-raw-transition-to-hom-core-shim.md`.

## Proved and sorry left

The assigned Sheaf module has zero declarations and zero `sorry`s.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. No proof-hole progress is claimed.
The existing upstream theorem was checked via the original shim with `lcompile.py`:
compiled in 7.8 seconds, and `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.
No delivered declaration contains a `sorry`.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore`,
a redundant public re-export of its canonical upstream module.
No other module or DAG node is pruned. All mathematical proof dependencies and the
unit route remain in place. The current source has no importers of the retiring
shim, confirmed by source search and `tools/downstream.py` (0 downstream modules).
The inventory's historical consumer now re-exports the upstream toHom module,
which imports the upstream core directly, so no consumer adaptation is required.
The core node already attaches to that exact upstream theorem. No DAG parent or
unit realization names the core node, and no rework or return entry matches it.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished proof, but the current item is
an explicit retirement assignment: the theorem has already been proved upstream,
and the Sheaf file contains only a compatibility re-export. The historical retire
inventory consumer has since become an upstream re-export too. The existing
node note still described the shim as exporting the theorem; this packet updates
that note to describe the actual retirement. No mathematical error or route
change is claimed, and no upstream declaration is removed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
