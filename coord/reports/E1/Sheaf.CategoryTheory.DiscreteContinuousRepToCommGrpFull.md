## What changed

Completed the queued retirement of
`Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull` in favour of
`WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull`.
The whole theorem/helper region is byte-identical to the upstream twin, including
its existing complete proof and local instance attributes. Migrated the sole
consumer's private proof import in
`Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux`; its declarations,
statements and proof bodies remain unchanged. The fullness node now records the
retained upstream theorem. Listed the duplicate module in `deleted.txt`.

Change record: `coord/changes/retire-discrete-continuous-rep-to-commgrp-full.md`.
No source-library file or target statement changes. No new node is introduced.

## Proved and sorry left

This retirement repair has zero original holes: proved 0 of 0 sorries;
0 holes added; 0 split off. No sorry remains in any delivered Lean module.
`Rep.discreteContinuousRepToCommGrp_full` was already completely proved and is
retained verbatim upstream, including the private pointwise-multiplication helper.
Its independent single-file compile succeeds and `#print axioms` lists only
`propext`, `Classical.choice`, and `Quot.sound`.

The adapted `Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux` and unchanged
`Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp` compile against the replacement.
All 34 current downstream import closures were checked; none gains a
Sheaf/upstream twin pair. The direct consumer changes exactly one import line.

## No longer needed

Retired `Sheaf.CategoryTheory.DiscreteContinuousRepToCommGrpFull`, whose sole
consumer no longer imports it. Its duplicate declarations are supplied by the
retained upstream twin. The mathematical node
`lem-exc-discrete-continuous-rep-to-commgrp-full` remains necessary: the parent
`lem-exc-discrete-continuous-rep-commgrp-compatible` retains its proof dependency
and uses the same theorem. The construction dependency
`def-exc-discrete-continuous-rep-to-commgrp` also remains necessary. No mathematical
lemma, unit step, source-library declaration or additional module is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished theorem, but the current item is
listed in `coord/retire-items.tsv` as retirement of an already proved duplicate.
The original SUPERSET entry recorded a dependency on the Sheaf construction copy;
that prerequisite has since been retired by K9. Both fullness modules now import
the same upstream construction, so the prior dependency obstacle is resolved.
There is no mathematical statement error. The DAG's former Sheaf attachment is
updated while its statement and proof route remain intact.

Read Stacks Tag 04JQ in `literature/stacks-project/etale-cohomology.tex`, the node,
its construction dependency, and the parent equivalence assembly. Searches with
`msearch.py` (LeanFinder, Loogle, grep) are recorded in `searches.jsonl`;
local searches locate the exact upstream implementation. The unit route is
preserved. The zero representation and arbitrary topological groups remain
covered by the unchanged statement and proof.

Process deviation during startup: used read-only `git status` and `git log` in
the shared repository despite the brief's no-git instruction. Those commands
changed no files. Stopped direct git inspection; packaging and delivery use only
the authorized `deliver3.py` workflow.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
