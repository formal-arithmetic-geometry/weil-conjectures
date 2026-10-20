## What changed

Restored `lean/Sheaf/Paper/GlobalTensorPullbackDerivedData.lean` from its quarantine
archive. Replaced only its retired public import
`Sheaf.Algebra.Homology.KFlatPullback` with the official upstream provider
`WeilConjectures.Algebra.Homology.KFlatPullback`.

The original archive fails because the public theorem signature cannot see the
ring map and inverse-image declarations. The corrected file compiles in 28.7
seconds without warnings. Its complete proof remains unchanged: K-flat pullback
gives derivability, the derivability API constructs the universal derived pair
and proves absoluteness, and normalized tensor descent supplies the tensor clause.
The private helper is proved, and every local instance retains its real construction.

The direct archived consumer `ModuleCupGlobalTensorPullback` was read at its
application of this theorem; its arguments and all returned clauses are unchanged.
An import scan including quarantined sources finds 49 indirect/direct consumers,
with exactly that one direct importer. No consumer is adapted or withdrawn.

Change record: `coord/changes/C2-global-tensor-pullback-derived-data-import.md`.

## Proved and sorry left

This is a zero-hole rework item: 0 holes before, 0 holes after, 0 holes closed,
0 holes added, and 0 split off.
`AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_derived_data` and
the private helper `exists_leftDerived_of_derives` retain complete proofs.
No `sorry` remains in any delivered Lean file.

## No longer needed

Removed the import of the retired empty module
`Sheaf.Algebra.Homology.KFlatPullback`, replacing it with its official provider.
No mathematical dependency, node, declaration, or module is pruned. Both
`GlobalTensorPullbackKFlat` and `GlobalTensorPullbackTensorDescent` remain needed.
The existing node's proof and dependencies agree with the unchanged Lean proof.

Searches: Lean Finder returned Tor declarations and exact derived-functor
comparisons, not this normalized K-flat comparison. Loogle did not recognize
`Functor.HasLeftDerivedFunctor`; msearch grep found no match. Direct source
search located the existing derivability API and the complete archived proof,
which is reused rather than replaced.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole, but this assignment is a quarantined
zero-hole import repair. The archived proof was already complete. Its public
import still named the now-retired Sheaf twin, so declarations in its public
signature became privately imported. The one import replacement repairs this
actual failure. No statement or DAG correction is needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
