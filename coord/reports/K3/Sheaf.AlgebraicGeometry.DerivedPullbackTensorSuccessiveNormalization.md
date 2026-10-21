## What changed

Restored lean/Sheaf/AlgebraicGeometry/DerivedPullbackTensorSuccessiveNormalization.lean
as a public compatibility import of the complete adopted source normalization proof.
The full source and archived theorem signatures are identical after the K-flat
predicate rename IsAcyclicTensorKFlat to IsKFlatTensor; those definitions have the
same acyclic-tensor body. All choices of composition comparison, tensorators,
ordinary adjunctions, counits, and the summand-normalized chain isomorphism are
unchanged. The source proof implements all three steps of the existing DAG plan.

Reattached lem-sc-derived-pullback-tensor-successive-normalization to the existing
source declaration, retaining all its statement and proof dependencies and its
three-step proof. Updated proof_origin to record the reused complete proof.
Change record: coord/changes/restore-derived-pullback-tensor-successive-normalization.md.
No source-library file, target, definition, or quarantined archive was changed.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived item had zero sorry holes;
the restored item has zero. Holes closed: none. Holes added: none. Split off: none.
The existing adopted proof of
AlgebraicGeometry.derivedPullback_tensor_successive_normalization is reused in full.
No theorem is left with sorry in this delivery. The complete declaration and its
axioms are checked through the restored import path.

## No longer needed

Removed the archived direct imports of
Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso,
Sheaf.Algebra.Homology.KFlatPullback, and
WeilConjectures.AlgebraicGeometry.PullbackTensorTotalCompositionLocalized.
The complete source proof obtains its normalized tensorator directly from
WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso and privately imports the
source KFlatPullback and PullbackTensorTotalCompositionLocalized modules.
The obsolete Sheaf KFlatPullback import is already a withdrawn empty module.
No mathematical node or module is withdrawn, and no proof dependency is pruned.
The unit route and the quarantined parent's dependency on this node are retained.
The local duplicate normalization_pasting proof and duplicate public normalization
declaration are supplied by the adopted source instead of being redeclared here.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine repair with zero holes, not an unfinished normalization
proof. The adopted library already contains the whole proof under the source path.
Its signature differs only in the name of the identical K-flat predicate. The
old direct Sheaf KFlatPullback import now supplies no declarations. A verbatim
restoration exceeded the single-file 60-second limit; the compatibility import
uses the canonical compiled proof and avoids re-elaborating the obsolete copy.
There are zero live importers, but the quarantined parent and its DAG still need
this normalization theorem. The packet therefore restores the path and preserves
the dependency rather than treating it as unused or withdrawing it.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
