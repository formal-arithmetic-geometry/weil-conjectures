## What changed

Retired the duplicate Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux,
listed in coord/retire-items.tsv. Its theorem docstring, signature and complete
proof are byte-identical to WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrpAux.
Changed the sole direct consumer Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp
to import the upstream theorem privately. Its existing public imports and global
forgetful-instance registrations are preserved, so indirect consumers retain the
same API. Redirected the existing node's Lean attachment to the upstream twin.
The proof, dependencies, mathematical statement and unit route remain unchanged.
No source-library file is edited.
The adapted consumer compiled on the project server in 2.0 seconds with no
warnings. The import-direction check found no cycle.

Change record: coord/changes/C8-retire-discrete-continuous-rep-commgrp-aux.md.

## Proved and sorry left

The item has zero sorries before and after retirement. Holes closed: none (0).
Holes added: none (0). No statements split off. The retained declaration
Rep.discreteContinuousRep_equiv_with_compatible_objectwise_iso already has the
same complete proof, via fullness, essential surjectivity and the whiskered
counit's naturality. This is a duplicate repair, not a new proof.

## No longer needed

Withdrawn module: Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux.
Removed its private proof import from Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp
and replaced it with the upstream twin. No mathematical node or proof dependency
is pruned: lem-exc-discrete-continuous-rep-commgrp-compatible remains needed and
attached to its preserved upstream declaration. The duplicate's imports disappear
with it; the adopted source twin and its prerequisite declarations remain intact.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but this is the listed
zero-hole duplicate retirement. The earlier SUPERSET obstacle is obsolete:
all three prerequisite modules now use upstream twins. The files differ in
public G-set imports and instance visibility, which is harmless specifically
because the sole direct consumer already supplies both the larger public import
and its own two global instance registrations. No mathematical error was found.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
