## What changed

Retired `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj`, an item
listed in `coord/retire-items.tsv`, in favor of its official upstream twin.
Their module bodies, including imports, local instances, statement, and proof,
are identical modulo whitespace. The prerequisite functor has already moved
upstream, resolving the earlier retirement blocker. Changed the sole direct
consumer `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux` to import the
upstream theorem. Its theorem statement and proof are unchanged. Repointed the
existing DAG node's Lean attachment, preserving all mathematical dependencies.

The returned head `d539d3b29a` was reconciled with the current auxiliary
module after E1's landing `bc0643a7d0`. The repaired packet preserves E1's
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull` import and
changes only the essential-surjectivity import relative to the current source.
The repaired auxiliary module compiled on the project server in 1.7 seconds
with no warnings. The earlier packet also compiled its unchanged immediate
consumer `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp`. The source-level downstream check found
34 modules, matching `tools/downstream.py`; only the auxiliary module imports
the retired copy.

Change record: `coord/changes/D4-retire-discrete-continuous-rep-ess-surj.md`.

## Proved and sorry left

The item began with zero holes. Closed: 0; added: 0; split off: 0; left: none.
`Rep.discreteContinuousRepToCommGrp_essSurj` remains fully proved by the
identical official upstream theorem. This is duplicate retirement, not a newly
claimed proof. No definitions, signatures, axioms, or target statements change.

## No longer needed

Withdrawn module: `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj`.
Removed its import from `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux`,
replacing it by `WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj`.
No mathematical nodes are pruned: the parent
`lem-exc-discrete-continuous-rep-commgrp-compatible` still cites
`lem-exc-discrete-continuous-rep-to-commgrp-ess-surj`, whose Lean attachment now
names the retained official proof. The unit's route remains intact.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but the current item is a
zero-hole duplicate-retirement item. The earlier kept-module note depended on
the functor's still being duplicated; K9's latest landing retired that copy and
adapted this module, so its official twin is now usable without a collision.
The complete existing proof is preserved upstream rather than restated.

The return identified a landing conflict between two adjacent proof imports,
not a mathematical defect. The old packet would have restored the retired
Sheaf fullness import; this repair takes the current file first and preserves
the upstream fullness import. No theorem body, signature, public import, or
instance was changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
