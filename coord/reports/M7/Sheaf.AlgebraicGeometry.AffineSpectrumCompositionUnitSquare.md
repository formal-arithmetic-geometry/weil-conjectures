## What changed

Restored `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare` as a
compatibility re-export of
`WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare`.
The upstream module already states and completely proves the exact theorem
`AlgebraicGeometry.affineSpectrum_composition_unit_square`, including the same
universes, derived-category instances, selected comparisons and original units.
Its abstract coherence proof follows the three associativity equations and two
unit laws in the existing node. Reusing it removes the duplicate declarations
and all obsolete local reducibility commands from the quarantined copy.
The node's Lean attachment now points to that upstream declaration.
No upstream file, target, definition, or theorem signature is changed.
The returned delivery at `2b4dbbb5ca` was compared with the current shared
`sheaf-dag` snapshot at `28f23e0d1ee`. At that snapshot the Sheaf path is still
absent from `lean/` and preserved in quarantine, and the upstream implementation
is byte-identical to the one used by the returned delivery. The restoration and
node reattachment therefore still apply. The compatibility file now explicitly
opens the public section required by the module convention. The retained
compatibility import compiled cleanly through `lcompile.py` in 1.3 seconds;
the final module with its explicit public section compiled cleanly in 1.5 seconds.
Comparing the current quarantined implementation with the upstream file confirms
that their declaration statements and proof bodies are identical: only the
copyright header, spacing and the obsolete local attribute differ.

## Proved and sorry left

The assigned rework is a zero-hole compilation repair, with an existing fully
proved upstream replacement for
`AlgebraicGeometry.affineSpectrum_composition_unit_square`
(node `lem-pc-affine-spectrum-composition-unit-square`).
The quarantined copy contained zero holes; the compatibility module contains
zero holes. Holes closed: none (0 of 0). Holes added: none. Split off: none.
The upstream proof and every one of its private helpers are complete.
This delivery claims reuse and pruning, not a newly closed proof hole.

## No longer needed

The duplicate abstract coherence implementation and concrete specialization in
the Sheaf copy are no longer needed: the upstream theorem supplies exactly the
same public statement. Its former direct public import of
`WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates` is now
provided through the upstream unit-square module. No underlying mathematical
proof dependency is pruned: the upstream proof uses the same three recorded
nodes. No additional theorem modules or new nodes are needed.
The former Sheaf implementation is pruned to a compatibility import.

## Where the brief, the DAG or earlier work was wrong

This item is quarantined rework, not an unfinished proof. Its old source is
`quarantine/Sheaf/AlgebraicGeometry/AffineSpectrumCompositionUnitSquare.lean`,
as recorded in `coord/rework.tsv`. Its local irreducibility attribute on
`derivedPullback` became invalid when upstream changed that definition to
`irreducible_def`. Initially removing that one redundant attribute compiled
cleanly in 24.9 seconds and passed a complete dry run, but later server compiles
of the duplicate proof timed out at 60 seconds, with no profiler trace returned.
The source search found the exact complete upstream theorem, so the final
repair reuses that theorem instead of recompiling duplicate proofs.
The old DAG attachment still named the quarantined Sheaf implementation;
it now names the existing upstream theorem, without changing the statement,
proof plan, dependencies, or unit route. No current `lean/` or `quarantine/`
module imports the old Sheaf path, so no consumer adaptations are required.

The return of 2026-10-20 was a stale-base landing refusal after review passed,
not a request to change the mathematical argument. Re-read the current rework
row, claim, quarantined implementation, node and upstream proof. Reapply the
restoration to the current `sheaf-dag` state through `deliver3.py`, which creates
its delivery commit on the freshly fetched base; no archive is deleted and no
upstream signature, attribute, public import or proof is edited.

Change record: `coord/changes/M7-affine-spectrum-composition-unit-square-rework.md`.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
