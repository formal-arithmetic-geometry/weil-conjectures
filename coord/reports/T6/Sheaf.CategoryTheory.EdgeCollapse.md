## What changed

Repaired the returned delivery ba738af137 against the current shared checkout.
The return reported an intervening write after base d92f73d8e. At this retry,
lean/Sheaf/CategoryTheory/EdgeCollapse.lean is absent in both the shared checkout
and the server working tree; its current original is retained under quarantine/.
Reconstructed the sandbox module from that current quarantined file and reapplied
the actual import-visibility repair: make
WeilConjectures.CategoryTheory.ExactCoupleConvergence a public import, because
its declarations occur in the public theorem signature. Remove four redundant
private imports. Everything below the import header is byte-for-byte unchanged.
The retained node equals the current node; no statement or proof route changes.

Verified on the current compile server: the quarantined original fails with
lean.invalidField for LimitSubobjects, AlphaColimit, ConvergesTo and the other
convergence declarations, explicitly recommending this public import. The
repaired module compiles cleanly in 1.7 seconds (exit code 0). The import-direction
check allows the import. This restores a working module, rather than merely
rebasing an unchanged library file. The delivery tool chooses the current base.
Change record: coord/changes/t6-edge-collapse-public-convergence.md.

## Proved and sorry left

Assigned quarantine/import build repair. Closed: zero of one original holes.
Added mathematical statements: zero. Split off: zero.
The actual delivered hole count is one:
CategoryTheory.BigradedExactCouple.edge_collapse (lem-sp-edge-collapse).
Its original named theorem proof remains sorry. Relative to the currently absent
lean/ module, restoration brings this one original hole back into the library;
relative to the quarantined original it adds zero holes. No definition has a hole.

## No longer needed

Removed redundant private imports:
WeilConjectures.Algebra.Homology.ExactCouple.Basic,
WeilConjectures.CategoryTheory.Abelian.Filtration,
WeilConjectures.CategoryTheory.ExactCouple, and
WeilConjectures.CategoryTheory.PBCFiltration.
Their needed source APIs are public dependencies of the convergence module.
Both original public Sheaf imports remain. No DAG node or module is pruned;
no source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The return correctly required rebuilding the packet from the current state after
an intervening write. The module is now quarantined, so there is no current file
at its former lean/ path to merge; the current quarantined declaration supplies
the complete original instead. Reapplied and reproduced the build repair against
that original. No stale replacement definition, withdrawal, or upstream proof
substitution is used. The sole defect addressed is import visibility; the
remaining edge-collapse proof is explicitly reported as unfinished, as permitted
for the assigned build repair.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
