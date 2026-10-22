## What changed

Restored the quarantined zero-hole item
Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat as a public
compatibility import of its existing adopted source implementation. The restored
module also publicly imports Sheaf.Algebra.Homology.KFlat to retain the legacy
IsAcyclicTensorKFlat predicate used by archived consumers.

The complete archived theorem statement AND proof are byte-for-byte equal to
WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat after
replacing IsAcyclicTensorKFlat with IsKFlatTensor. Both predicates have identical
definition bodies. The full tensor/composition identity, universal assumptions,
chosen comparison, counits and tensorators are preserved. The native theorem
already proves the four-step plan by normalization, counit factorization,
naturality and cancellation; no new reduction or split is needed.

Updated only the existing node's lean attachment to the actual source module and
its verbatim signature. The mathematical statement, stmt_deps, proof, proof_deps,
proof_origin and unit route are unchanged. The quarantine archive is retained;
there is no deleted.txt and no source-library edit or forced adaptation.

Change record:
coord/changes/F4-restore-derived-pullback-composition-tensor-kflat.md.

Validation: the restored module compiled in 1.7 seconds. A two-file consumer check
compiled the restored module in 2.1 seconds and the audit in 7.0 seconds. The audit
imports only the restored path, proves the legacy/source predicate equality by rfl,
and applies the existing theorem at the complete verbatim archived signature.
All checks use lcompile.py on the project server. The import-direction check passes.
A source comparison asserts full theorem-and-proof identity after only the K-flat
predicate rename. The node comparison confirms lean is the only changed field.

## Proved and sorry left

Assigned restoration repair with zero original textual sorries. Holes closed: 0.
Holes added: 0. Holes remaining in the restored module: 0. No split or decomposition.

AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat
(node lem-sc-derived-pullback-composition-tensor-kflat) reuses its existing complete
source proof. This packet restores the unavailable import path and preserves the
existing theorem; it does not count inherited proofs as newly closed holes.
No declaration in this packet has a sorry. The explicit #print axioms check for
AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat prints exactly propext,
Classical.choice and Quot.sound, with no sorryAx or other axiom.

## No longer needed

No mathematical node or library module is pruned. Every dependency and the
quarantined parent's use remain necessary and recorded.

The archive's direct imports
Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso,
Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison (all), and
Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization are replaced
by the adopted theorem's public import. Their mathematics remains in the adopted
proof's import closure. Its public GlobalHomAdjunctionIso import provides exactly
the former MixedHomTensorPullbackIso compatibility module's public API.
The additional legacy KFlat import is needed for consumers using the old predicate.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open hole, but the rework row identifies
this actual assignment as a missing quarantined module with zero holes. Restoring
the archive verbatim would duplicate an existing source theorem. The proper
repair reuses that theorem and checks the complete archived statement against it.
The DAG attachment still named the unavailable Sheaf implementation; it now
identifies the existing source declaration without withdrawing its obligation.

Read the current return file (only the standing sync notice) and rework row.
The downstream tool reports zero live users because the assigned path is absent;
a separate quarantine search finds MixedPullbackSquareTensorCoherence, whose
line 167 applies this theorem. Its node still cites this item in proof_deps and
proof-step uses. Both are preserved. The adopted version of that parent already
imports the native theorem, so it needs no adaptation. The unit's realized route
remains unchanged; this compatibility restoration bypasses no unit step.

Searches through leanfinder, loogle and grep found only generic Mathlib tensor
calculus. Direct source search found the exact complete adopted theorem, so no
new chain lemmas or duplicated theorem proof are introduced. Identity arrows,
zero complexes and empty schemes retain the original theorem's unrestricted
hypotheses and conclusion.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
