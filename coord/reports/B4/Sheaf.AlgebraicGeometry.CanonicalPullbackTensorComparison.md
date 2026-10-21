## What changed

Repaired the zero-hole quarantine item by restoring
lean/Sheaf/AlgebraicGeometry/CanonicalPullbackTensorComparison.lean as a compatibility
module importing the existing adopted-source implementation. A public import preserves
its public API; a public import of Sheaf.Algebra.Homology.KFlat preserves the
inherited legacy K-flat names. An additional private import all preserves helper
access for archived import-all consumers. No WeilConjectures source file is changed.

Repointed the two existing node lean records to the actual source module, preserving
their declaration names, statements, proof steps and proof dependencies. The source
already contains the full model-transport, existence and uniqueness proofs.
The quarantine archive is retained and no deleted.txt is used.

Change record: coord/changes/canonical-pullback-tensor-source-compatibility.md.

Validation: restored module compiles; all three archived definitions equal the source
definitions by rfl in a compiled audit (14.3 seconds). A separate consumer imports all
of the restored Sheaf module and checks the canonical predicate, model transport,
existence, uniqueness, counit_isIso and modelMap_isIso (2.7 seconds).
The final consumer audit also publicly uses IsAcyclicTensorKFlat and
IsKFlatResolution and applies both helpers with the old K-flat predicate;
it compiles in 5.8 seconds. The final compatibility module compiles in 3.8 seconds.
Full restoration of the other quarantined consumer dependencies is outside this
packet. Import direction check passes.

## Proved and sorry left

This is an assigned repair with zero original textual sorries. Holes closed: zero.
Holes added: zero. Holes remaining in the restored module: zero. No decomposition.

AlgebraicGeometry.exists_canonical_from_model,
AlgebraicGeometry.exists_canonicalPullbackTensorComparison and
AlgebraicGeometry.IsCanonicalPullbackTensorComparison.unique are reused from the
already proved adopted source. Their downstream mathematical dependencies are
unchanged; this repair makes no claim of closing holes in those other modules.

## No longer needed

No mathematical node or module is pruned. Both node attachments and every proof
dependency are preserved. The duplicate archived implementation is replaced by
reuse of the existing source implementation.

The archive's direct imports Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel,
WeilConjectures.AlgebraicGeometry.DerivedTensorStructure,
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition,
WeilConjectures.AlgebraicGeometry.ModulePullbackTensor,
Mathlib.Algebra.Homology.Monoidal and Sheaf.Algebra.Homology.KFlatPullback are no
longer needed as direct imports of this compatibility file. The corresponding
mathematics is still used by the source implementation and remains in the DAG.
The adopted CanonicalPullbackTensorComparison is imported publicly for its API
and privately with all for helper access. Sheaf.Algebra.Homology.KFlat remains a
public compatibility dependency to preserve legacy names in consumer signatures.

## Where the brief, the DAG or earlier work was wrong

The assigned module has no sorry: it is a quarantine restoration repair.
The archive imports an absent Sheaf monoidal-model module, while the current source
already supplies this entire implementation. The retirement census marked the
canonical predicate DIFFERENT due to the K-flat predicate rename; full definitional
equality checks establish that it preserves the archived mathematical meaning.
Both old node records pointed at the missing Sheaf file; they now identify the
adopted source declarations without dropping any attachment or dependency.

Zero live importers would miss the twelve quarantined direct consumers. They remain
accounted for in the change record, including private helper access in
DerivedPullbackCompositionTensorKFlat. The unit route is unchanged.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
