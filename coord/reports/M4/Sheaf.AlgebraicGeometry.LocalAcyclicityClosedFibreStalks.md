## What changed

Restored `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreStalks` from its
quarantine source, preserving the complete statement and original public import.
Replaced its withdrawn private stalk-formula import with
`WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`.
Added the private `StrictHenselizationClosedFiberComparison` import and an explicit
cohomology transport between the two canonical strict-local models. The induced
pullback isomorphism is constructed by two pullback lifts; its projection equation
transports the coefficient sheaf. `singleFunctorιIso` supplies the ambient-derived
single object. The existing private cohomology-invariance helper is reused.

Updated the item's DAG proof and proof dependencies with the actual model transport.
Change record: `coord/changes/M4-local-acyclicity-closed-fibre-stalks-restoration.md`.
The sole archived consumer's signature and usage are preserved; no forced adaptation.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 existing holes, 0 holes closed, 0 added,
0 split off, 0 remaining. The restored theorem is
`AlgebraicGeometry.Etale.closedFibre_derivedUnit_target_stalks`, node
`lem-weil-pbc-local-acyclicity-closed-fibre-stalks`.
Its archived private helper `nonempty_cohomology_iso_of_iso_over` remains proved.

The repaired file compiled in 12.4 seconds without warnings after import pruning.
`#print axioms AlgebraicGeometry.Etale.closedFibre_derivedUnit_target_stalks`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the private import of the withdrawn empty module
`Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`; the mathematical
stalk-formula dependency is retained through the official WeilConjectures module.
Removed the unused private import `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
All original mathematical proof dependencies remain needed. No DAG node or
additional library module is withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined zero-hole restoration, not a new sorry-filling task.
The archived import refers to an empty retired twin. The existing stalk-formula
node's Lean attachment still points at that retired twin, whereas the actual
upstream theorem now uses the full strict-local model. Simply changing the import
therefore leaves a genuine model mismatch. The delivered explicit pullback and
cohomology isomorphisms repair that mismatch without changing the assigned statement.
The small/full comparison is an existing proved tool, not a replacement for any
unit step. The source argument of Tag 0GJU still computes the same stalks, including
q = 0, positive degrees and empty fibres; no acyclicity, torsion or properness
hypothesis is added. No new nodes.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
