## What changed

Restored `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence`
from its quarantine assignment as a public re-export of the adopted source module
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence`.
The public theorem `AlgebraicGeometry.tensorHomUncurry_representative_coherence`
already has a complete proof there. Its canonical K-flat predicate is `IsKFlatTensor`;
the old `IsAcyclicTensorKFlat` definition has exactly the same body. Re-exporting avoids
both the original invalid-field error and a second declaration of the same name.

Preserved the DAG node's assigned Sheaf module/file attachment, mathematical statement,
and both proof dependencies. Updated its recorded Lean signature and proof provenance.
The proof still factors through normalized identity evaluation, combines the two
heterogeneous equalities, and uses precisely the two stated proof dependencies.
No adopted source declaration, target, definition, or unit route changes.

Change record: `coord/changes/tensor-hom-representative-canonical-reexport.md`.

## Proved and sorry left

This is a zero-hole interface repair: 0 of 0 local sorries closed, 0 holes added,
0 split off, and no sorry left in the restored item. The existing complete theorem is
publicly available through the restored import. Neither private helper nor the public
theorem is redeclared. No new proof hole or data construction is introduced.

The restored module compiles through `lcompile.py` (2.3 seconds, exit 0). A second
compile checked the exported theorem and printed its axioms (1.6 seconds, exit 0):
exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.

## No longer needed

The archived module's direct imports of
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential`,
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation`, and
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomIdentityEvaluationCoherence`
are supplied by the canonical source theorem module. All three are still needed by
that module; no mathematical dependency or node is pruned. The duplicate local
implementation and its two private helpers are unnecessary because the source library
already proves them. No module is withdrawn, no `deleted.txt` is used, and no DAG
attachment or dependency is removed. The quarantined parent and its DAG dependency
were checked and preserved.

## Where the brief, the DAG or earlier work was wrong

The quarantine failure is an upstream-migration mismatch, not an unfinished proof:
the archived file has no sorry. Its imports now expose `IsKFlatTensor` instead of
`IsAcyclicTensorKFlat`. Reintroducing an identically named local theorem would also
collide with the adopted theorem when both modules are imported. The shortest repair
is to reuse the canonical proof and retain a nonempty public forwarding module.

Library grep found the exact adopted theorem. LeanFinder returned only generic
monoidal localization and Tor facts; Loogle returned HEq transport primitives.
The assigned node's two declared dependencies are fully proved upstream and match
its proof. The unit `sk-thm-picard-duality` has empty realized statement/step lists;
its route stays intact. `tools/downstream.py --allow-missing --uses` reports zero live downstream modules and
zero live callers. Searches through quarantine additionally found the archived parent.
The only archived direct consumer has independent stale
K-flat syntax, so this packet does not restore or alter that separately quarantined item.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
