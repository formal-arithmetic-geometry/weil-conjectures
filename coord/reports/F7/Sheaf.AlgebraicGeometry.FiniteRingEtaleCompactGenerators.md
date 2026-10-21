## What changed

Restored `Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators` from its
quarantine archive, preserving `AlgebraicGeometry.Etale.finiteRing_compactGenerators`
and its complete proof. Replaced the public import of the retired Sheaf compact-object
module by `WeilConjectures.CategoryTheory.CompactObject`. Replaced the private import
of the retired Sheaf constructibility comparison by its source-library counterpart,
and renamed the single comparison application to
`Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`.

The node retains its Lean attachment, statement, proof dependencies and unit route;
its proof text now names the current comparison theorem. The change record is
`coord/changes/F7-finite-ring-etale-compact-generators-restoration.md`.

## Proved and sorry left

This is a zero-hole repair. The restored theorem
`AlgebraicGeometry.Etale.finiteRing_compactGenerators` has a complete proof.
Holes closed: zero of zero. Holes added: zero. Holes remaining: none.
No lemmas were split off. Existing dependency theorems are used as stated.

## No longer needed

Removed the imports `Sheaf.CategoryTheory.CompactObject` and
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`, both retired
empty modules, replacing them with the canonical source modules. No mathematical
node or dependency is pruned: all existing proof dependencies remain needed.
No archive or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The live item is absent because it was quarantined, not because it was withdrawn.
The archive used the retired compact-object module and the retired short comparison
name. The original server compile diagnosed `IsCompactObject` as privately imported
in the public signature and the old comparison theorem as unknown. The canonical
source imports and comparison name repair those errors without changing the statement.
The existing D9 retirement record explicitly prescribes the comparison migration for
this quarantined consumer. A later compile attempt received exit 124 (busy server)
and is retried; this is not treated as a mathematical or tool defect.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
