## What changed

Completed the queued retirement of
`Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp` in favour of
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrp`.
The eight public declarations have matching signatures and bodies; only the
forgetful-instance source differs. Updated the public imports in the fullness and
essential-surjectivity consumers and locally enabled the upstream discrete/type
forgetful instances. Their signatures, visibility, and proof bodies are unchanged.
Updated the definition node's Lean attachment to the official twin and listed the
retired module in `deleted.txt`.

Change record: `coord/changes/retire-discrete-continuous-rep-to-commgrp.md`.
The upstream sources, target statements, and blueprint unit route are preserved.

Reconciled the returned packet with the current shared source after A9's landing
`212359aa7b`: the retired module now publicly imports
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets`, rather than its former Sheaf
copy. Compared that current file with the retained upstream twin: everything
from `variable (G : Type u)` through `end Rep` is byte-identical. The retirement
still removes the duplicate construction, migrates both consumers, and preserves
the node through its upstream attachment. The replacement uses the same named
forgetful instances, enabled locally in both consumers. Delivery is rebuilt from
the current source, rather than from the returned base `d92f73d8e`.

## Proved and sorry left

This is a retirement repair with zero original holes: proved 0 of 0 `sorry` holes;
0 holes added; 0 split off; no `sorry` remains in the delivered consumers.
The eight existing proofs/constructions are retained verbatim in the upstream twin,
including `Rep.discreteContinuousRepToCommGrp_faithful`.

Both adapted consumers compiled cleanly. The unchanged
`Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux` and
`Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp` also compiled against them.
All 36 current downstream import closures were checked for newly introduced twin pairs;
none were found, and no consumer still imports the withdrawn module.

## No longer needed

Retired `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrp` (all eight duplicate
declarations); its two direct consumers no longer import it. The node
`def-exc-discrete-continuous-rep-to-commgrp` remains needed and now points at the
official upstream twin. No mathematical dependency or blueprint step is pruned.
The current public import of `WeilConjectures.AlgebraicGeometry.EtaleFieldGsets` is unnecessary
for this construction; the twin uses the smaller geometric-action interface.
The unchanged equivalence modules still publicly import the upstream G-set equivalence, so its
own module and node are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described an item containing `sorry` or needing a
construction repair. The queue and `coord/retire-items.tsv` identify this item
specifically as retirement of an already proved duplicate with two consumers.
No mathematical statement was wrong. The import API differs: the official twin's
forgetful instances are local rather than the copy's exported global instances;
the consumer-local attributes account for that difference.

The return identified an overlapping import migration by A9, not a proof defect.
The previous packet's description of a Sheaf G-set import was stale. The current
shared source and both direct consumer files have been checked again; their
construction/proof bodies still match the implementation retained by retirement.

Searches used `msearch.py` (LeanFinder, Loogle, and grep), with results in
`searches.jsonl`. Loogle found the general representability infrastructure;
local searches and the full twin comparison found the exact retained implementation.
No new statement, new module, or new node is introduced.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
