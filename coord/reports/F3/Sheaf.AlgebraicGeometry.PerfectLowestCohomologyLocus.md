## What changed

Restored lean/Sheaf/AlgebraicGeometry/PerfectLowestCohomologyLocus.lean from its
quarantine archive. Replaced the withdrawn Sheaf derived-pullback public import
with the adopted WeilConjectures derived-pullback and tensor-pullback public imports.
The theorem exists_perfectLowestCohomologyLocus, its full signature, its proof, and
its DAG attachment lem-sc-perfect-h0-locally-closed are preserved.

The restored module compiles cleanly through lcompile.py. The proof still obtains
the rank-bound open, constructs the closed matrix locus within it, proves the two
factorization implications, and applies the universal lowest-cohomology pullback
comparison. All three recorded proof-dependency modules are used. Edge cases r = 0,
empty schemes, and empty amplitude intervals require no additional hypotheses in
this assembly. The unit route is unchanged. Consumer audit and import rationale are
in coord/changes/F3-perfect-lowest-cohomology-locus-restoration.md.

## Proved and sorry left

This is a zero-hole quarantine repair, not a new proof or decomposition.
AlgebraicGeometry.Scheme.exists_perfectLowestCohomologyLocus retains its complete
existing proof. Holes in the archive: 0. Holes closed: none (0). Holes added: none
(0). Holes left in the delivered module: none (0). No statements were split off.
Dependencies may retain their own existing proof obligations; none is changed here.

## No longer needed

Removed the public import Sheaf.AlgebraicGeometry.DerivedPullback, which is already
an empty withdrawn duplicate. The statement now uses the adopted upstream API.
No mathematical node, proof dependency, or module is newly pruned or withdrawn.
All three recorded proof dependencies remain needed. LeanFinder found ordinary
module free-locus lemmas, not this derived universal rank-locus statement; Loogle
and project grep found no replacement for the existing three-lemma assembly.

## Where the brief, the DAG or earlier work was wrong

The assigned source was quarantined, not absent mathematical work: coord/rework.tsv
preserves its archive. The archive already had zero sorries. Its obsolete public
import failed to expose derivedPullback and tensorPullback after adoption of the
upstream definitions. The compiler identified both missing public imports; this
repair follows those suggestions. The DAG proof matches the retained Lean proof
and needs no change. No consumer signature or target statement changes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
