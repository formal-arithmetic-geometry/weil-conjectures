## What changed

Repaired the quarantined module by restoring it as a public compatibility import of
WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison.
Its canonical upstream theorem has a byte-identical signature and proof body to the
archived theorem. The DAG lean attachment now points to that existing declaration;
its statement, proof, proof_deps and unit route are unchanged. No source-library
file is edited, no archive is deleted, and no duplicate declaration is introduced.

The original full proof was first restored in the sandbox, with its derivedPullback
import redirected upstream and the redundant local irreducibility attribute removed;
it compiled in 8.3 seconds. The final packet uses the existing upstream proof instead.
The final compatibility module compiled in 1.5 seconds. A sandbox check importing
both module paths and both existing consumer modules compiled in 1.6 seconds.
#print axioms on the canonical theorem lists exactly propext, Classical.choice,
and Quot.sound, with no sorryAx. The temporary check is retained only in scratchpad.
Change record: coord/changes/A6-derived-projection-mate-quarantine-restoration.md.

## Proved and sorry left

This is a zero-hole import/quarantine repair. The archive had zero textual sorries;
the restored module has zero. Holes closed: none (0 of 0). Holes added: none.
Split off: none. The already-proved declaration is
AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison
(node lem-pc-derived-projection-mate-open-restriction-comparison).
No unfinished proof is handed on, and no proof-dependency hole is added.

## No longer needed

The duplicate Sheaf declaration and its private mate_square helper are unnecessary:
the canonical upstream module contains the same complete proof. Its old imports
are supplied through the upstream module. The withdrawn
Sheaf.AlgebraicGeometry.DerivedPullback import is replaced by the canonical upstream
import closure. The three proof dependencies (derived-open-restriction-qcoh-iff,
open-restriction-adjunction-hom-descent, open-restriction-tensor-counit-descent)
remain necessary and remain recorded. No DAG node or mathematical module is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned path is absent from lean and must be read from its quarantine archive,
as coord/rework.tsv records. It already has a complete proof and zero holes; the
repair is the import collision after the upstream sync. The upstream counterpart
now supplies the exact same declaration. The historical retirement inventory marked
this twin DIFFERENT because of dependency collisions; the present restored proof
compiles against the canonical upstream dependency closure. Searches found no
shorter Mathlib projection-mate theorem (LeanFinder: eight related underived hits;
Loogle: Arrow.isoMk and its four projection lemmas; grep: no exact Mathlib hit).
The actual shortest library route is the existing upstream theorem.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
