## What changed

Retired `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` as explicitly assigned
by the human's retirement hand-off. The wrapper is absent from the sandbox and listed
in `deleted.txt`. Its complete theorem remains in the unchanged official module
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth`.

The listed consumer, `Sheaf.RingTheory.ResidueFieldProjectiveDimension`, already imports
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimension` after M1's landed repair
8bdeee4c0a. That source module imports the official depth module and uses the current
categorical projective-dimension API. The consumer is included unchanged for compilation;
there are no consumer edits to land. No active Lean module imports the retired path.

The node `lem-weil-pbc-residue-field-pd-le-depth` already points at the official theorem.
Its attachment note now records the wrapper's retirement; its statement, declaration,
proof, proof dependencies, and unit route are preserved. The change record is
`coord/changes/retire-residue-field-projective-dimension-depth-A4.md`.

Validation: the listed consumer compiled individually through `lcompile.py --all`
with exit code 0 and no warnings. A scratch consumer imports the official depth
module and the listed Sheaf dimension consumer, applies the canonical depth bound,
and prints axioms of both bounds: only `propext`, `Classical.choice`, and `Quot.sound`.
It compiled with exit code 0. `tools/downstream.py` reports zero downstream modules;
a search of active Lean sources finds no reference to the retired import path.

## Proved and sorry left

Zero initial holes, zero holes closed, zero holes added, and zero holes left in the
retired wrapper or listed consumer. No split-off statements. The existing proved
`Ring.residueField_projectiveDimension_le_depth` and
`Ring.residueField_projectiveDimension_le_ringKrullDim` remain unchanged upstream.

## No longer needed

Module `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` and its compatibility
public import of `WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth`.
The wrapper defines no declarations, and no active Lean consumer refers to it.
The mathematical node and all its dependencies remain needed and are retained on
the official source theorem. No other module or mathematical dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The retirement inventory predates M1's synchronization repair. Its DIFFERENT API
classification and listed consumer describe the earlier full Sheaf copy; the current
source is a declaration-free public-import wrapper, and M1 has already migrated the
consumer and DAG attachment. Thus retirement requires withdrawal of the remaining
wrapper rather than repeating an API adaptation. The earlier sandbox's no-op report
addressed a stale rework assignment; this packet performs the newly requested retirement.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
