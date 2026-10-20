## What changed

Restored lean/Sheaf/RingTheory/BoundedProjectiveResolutionDimension.lean from its
quarantined import interface as a public import of
WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension. The source module
already proves precisely ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE.
This eliminates the local duplicate declaration and the incompatible direct definition
imports while preserving the historical Sheaf import path for quarantined consumers.
No upstream file or declaration is changed; no archive is deleted.

Read the current rework row, E2 return record, A3 retirement change record, bridge node,
its dependency nodes, the upstream bridge and splice proofs, and Stacks Algebra 065R.
The unit route and current upstream node attachment are unchanged. Search with
msearch LeanFinder found the Mathlib dimension and Ext criteria; Loogle reported no
match; local rg found the exact adopted upstream proof. Thus no new proof is needed.

Compiled the restored module and, separately, the unchanged upstream bridge and splicing
modules. A temporary consumer probe checks the unchanged bridge signature and both
.mp/.mpr applications when both module paths are imported together. The bridge's
#print axioms reports only propext, Classical.choice, Quot.sound. Scratch sources are
excluded from the packet.

Change record: coord/changes/bounded-projective-resolution-dimension-reexport.md.

## Proved and sorry left

Zero original sorries (the quarantined source already has a complete proof).
Zero holes closed, zero holes added, zero split off, zero sorries left.
ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE remains fully proved
in the upstream module, with its existing node
lem-weil-pbc-projective-resolution-ext-degree. This is a zero-hole interface repair,
not new proof progress or a decomposition.

## No longer needed

Removed the restored module's direct public imports of Sheaf.RingTheory.GlobalDimension
and Mathlib.CategoryTheory.Abelian.Projective.Dimension, and its private imports of
Mathlib.CategoryTheory.Abelian.Projective.Ext and
WeilConjectures.RingTheory.ProjectiveResolutionSuccSplice; the public upstream bridge
import supplies the required interface and retains its own proof dependencies.
Removed the duplicate local bridge body. No mathematical node, dependency or upstream
module is pruned: the bounded-resolution predicate, Ext criteria and splicing construction
remain necessary to the upstream proof. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it was quarantined after the upstream
sync, not because its mathematics was withdrawn. Its preserved source contains zero
sorries. The current bridge node has already been reattached to the complete upstream
proof by the reviewed A3 GlobalDimension retirement. Restoring the old local declaration
would reintroduce a duplicate; replacing the absent path by an empty module or deleting
its archive would break quarantined consumers. A public reexport restores their import
interface with a single shared declaration and definition environment.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
