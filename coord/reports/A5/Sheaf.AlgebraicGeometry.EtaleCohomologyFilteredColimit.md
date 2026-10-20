## What changed

Retire Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit via deleted.txt,
in favor of WeilConjectures.AlgebraicGeometry.EtaleCohomologyFilteredColimit.
The retirement is assigned by coord/retire-items.tsv. The three listed Sheaf
consumers have already been retired in the current shared repository, and their
upstream versions already import the twin. No remaining Lean module imports
the duplicate, and no DAG node has lean.module pointing to it.

No upstream file or target statement is changed. The upstream module theorem
has a smaller index universe than the duplicate, but no remaining consumer
uses that duplicate theorem or needs an adaptation.

Change record: coord/changes/A5-retire-etale-cohomology-filtered-colimit.md.

## Proved and sorry left

Repair/retirement with zero original holes: proved 0 of 0 sorries, added 0,
split off 0, and left 0 in the withdrawn module. Both existing public theorem
names remain supplied by the upstream twin. No new declaration is introduced.

Validation: tools/downstream.py reports zero downstream modules; an exact
source import scan and DAG attachment scan return no users. A remote lcompile
probe imports the upstream twin and all three former consumers together,
checks the available theorem signatures, and compiles cleanly (1.8 seconds).

## No longer needed

The entire duplicate module
Sheaf.AlgebraicGeometry.EtaleCohomologyFilteredColimit is no longer needed.
Its proof-only import of Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit
is removed with it; that separate module is not withdrawn in this delivery.
The duplicate's other imports remain available wherever the upstream proof
uses them. No source-library declaration or dependency is pruned.
No DAG attachment or unit route changes.

## Where the brief, the DAG or earlier work was wrong

This is a retirement item with no sorry, rather than an unproved theorem item.
The queue's three consumer entries are stale: the corresponding Sheaf files
have already disappeared and the upstream versions import the twin.
The earlier note saying retirement would introduce an import cycle describes
an older source arrangement; the current upstream twin and consumers already
use the upstream route.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
