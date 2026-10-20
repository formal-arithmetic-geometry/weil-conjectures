## What changed

Withdraw the unused Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity
compatibility re-export. The canonical upstream identity theorem and its complete
upstream normalized-edge consumer remain verbatim. Correct the consumer node's
proof and proof_deps to record its existing use of the identity theorem followed
by equality elimination and Iso.ext. Keep the identity node attached to its
canonical provider, retaining all of its proof steps and mathematical dependencies.

Change record: coord/changes/E2-affine-identity-wrapper-pruning.md.

## Proved and sorry left

Current item: zero declarations and zero sorries before withdrawal; zero sorries
afterward. Holes closed: none. Holes added: none. Split off: none. This delivery
prunes an unused module and claims no new theorem proof or decomposition.

The existing complete proofs of
AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity and
AlgebraicGeometry.exists_affinePushforwardCohomologyEdge are retained. The latter
is the actual direct consumer and already imports the canonical upstream identity
provider. Server compilation of the complete proofs and #print axioms verify the
replacement route. The consumer and identity theorem use only propext,
Classical.choice and Quot.sound.

## No longer needed

Module pruned: Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity.
The wrapper's public import of
WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity is removed
only from this unused compatibility path. The upstream provider and every
upstream public and private import remain intact. No mathematical node is pruned.
The coordinate, sheaf-edge, adjunction, and factorization dependencies all remain
reachable along the corrected consumer-to-identity route. There are no current
or quarantined importers of the removed path and no unit realization of it.

## Where the brief, the DAG or earlier work was wrong

The assignment describes a holed deep-chain item, but the current source already
contains a reviewed zero-hole re-export and the adopted upstream proof is complete.
Reuse it. The consumer node's previous proof description omitted its actual call
to the identity theorem; this packet records that call and preserves the full
mathematical argument transitively. Neither a renamed hole nor a new split is
needed. The quarantine archive, source-library declarations and target signatures
remain unchanged.

Searches run through msearch.py: LeanFinder returned generic affine-scheme API,
Loogle did not know the project-local identity theorem name, and the Mathlib grep
found no such project theorem. Direct rg of the library found the exact complete
upstream provider and its normalized-edge consumer. tools/downstream.py reports
zero modules downstream of the assigned Sheaf wrapper; current and quarantined
source searches confirm it.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
