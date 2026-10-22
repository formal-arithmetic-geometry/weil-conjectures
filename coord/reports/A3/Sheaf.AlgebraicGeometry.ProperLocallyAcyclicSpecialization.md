## What changed

Restored Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization from the archive
specified by its coord/rework.tsv row. Added the explicit public import
WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence, which defines
rightDerivedLowerStarPlus used in the public theorem statement. The unchanged archive
failed with a privately imported public-name error at line 300; the repaired file
compiled cleanly in 23.2 seconds. All theorem signatures, docstrings, proof bodies
and the DAG attachment and proof route are preserved.

The proof follows Stacks Tag 0GJW for G[0]: torsion homology and proper base change
make the fibre maps invertible; qcqs torsion preservation and strict-local exchange
make restriction and cospecialization invertible; compatibility then gives derived
specialization, and exact-stalk homology gives the displayed specialization map.
Existing library declarations supply every nontrivial dependency. LeanFinder,
Loogle and grep searches found no replacement theorem for this particular statement.

Change record: coord/changes/A3-restore-proper-locally-acyclic-specialization.md.

## Proved and sorry left

This is a restoration and visibility repair, not a newly closed hole. The archived
and delivered modules both contain zero sorry proofs: 0 holes closed, 0 holes added,
0 split off, 0 left. The restored theorem is
AlgebraicGeometry.Etale.isIso_etaleStalkSpecialization_of_proper_locallyAcyclic,
node lem-weil-pbc-proper-locally-acyclic-specialization; all nine existing private
helper theorems also retain their complete proofs.

## No longer needed

None. No imports, nodes or modules are pruned. In particular, the quarantined
SmoothProperPrimeSpecialization parent still needs the theorem. All recorded proof
dependencies and the unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole rework item, not a module with an open proof. The quarantined
archive relies on a private proof import to provide rightDerivedLowerStarPlus in
its public signature. Its defining coherence module must be publicly imported.
The earlier landed A3-module-specialization-generic-restriction change record already
describes that fix, but the current live path is absent and its archived file still
has the failing import list. This delivery restores the archive with that concrete
repair. There is no mathematical statement correction or DAG route change.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
