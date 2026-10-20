## What changed

Restored lean/Sheaf/AlgebraicGeometry/ResidueStalkHomologyMapComparison.lean
from its rework quarantine archive. Replaced its public import of the retired
Sheaf.AlgebraicGeometry.DerivedPullback with the canonical
WeilConjectures.AlgebraicGeometry.DerivedPullback. This repairs the recorded
upstream-sync import collision. No other Lean lines change.

The server compile passed without warnings in 12.2 seconds. Import-direction
checking permits the canonical import. Both existing proof dependencies were
read: the natural open restriction comparison supplies invertibility of the
localized derived arrow, and the simultaneous strictly-perfect comparison
transfers it to the termwise residue-stalk homology arrow. The single restricted
unit is strictly perfect by the existing private proof. The existing DAG route
and unit route are retained verbatim; no node edit is needed.

Change record: coord/changes/P4-residue-stalk-homology-canonical-pullback.md.

## Proved and sorry left

This is a zero-hole quarantine repair. The restored public theorem
AlgebraicGeometry.isIso_residue_stalk_homologyMap and the private helper
strictlyPerfect_single_restricted_unit retain their complete proofs.
Original holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
No statement is split off. This packet does not claim new proof progress.

## No longer needed

Removed the import Sheaf.AlgebraicGeometry.DerivedPullback, whose empty retired
module is replaced by the canonical upstream import. No mathematical node or
proof dependency is pruned; both existing comparison lemmas remain necessary.
The quarantine archive and all parent dependency records remain intact.

A fresh Loogle search for HomologicalComplex.homologyMap, CategoryTheory.IsIso
returned only generic homology-map isomorphism lemmas; no replacement for the
geometric comparisons. Local source searches found no duplicate public theorem.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described a possibly holed item, but this assignment is
a rework restoration with zero holes. The archive's old derived-pullback import
was stale after the canonical upstream migration. The DAG already names the
canonical definition and accurately describes the retained complete argument.
The downstream script cannot enumerate a quarantined module; direct searches
of active and quarantined Lean sources and DAG parent records were used instead.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
