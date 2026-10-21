## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardTermwiseSourceCoherence.lean from its
recorded quarantine archive, preserving its public import, theorem signature,
universes, and canonical comparison construction. Replaced the final manual
precomposition-and-simp argument with Mathlib Iso.eq_inv_comp applied to the
existing picardTermwiseSingleMap_composition equation.

The structure sheaf is invertible, so isIso_canonicalSinglePullbackMap makes each
explicit picardTermwiseSingleMap invertible. Their asIso family satisfies the
required equality by the stated composition theorem. This applies to empty
schemes, identity maps, and zero structure sheaves without new hypotheses.

The restored module compiled cleanly through lcompile.py in 19.7 seconds.
A direct signature comparison agrees with the existing node exactly.

Change record: coord/changes/M4-picard-termwise-source-coherence-restore.md.

## Proved and sorry left

Restored the complete proof of
AlgebraicGeometry.Scheme.picard_termwise_source_coherence
(node lem-sc-picard-termwise-source-coherence).
The archived item contains zero sorry holes. Holes closed: 0. Holes added: 0.
No sorry remains in the delivered module. This is restoration of a quarantined
proved theorem, not a new hole closure or a decomposition.

## No longer needed

None. Both original imports and all four stated proof dependencies are retained.
No node, module, declaration, public import, or unit step is withdrawn. In
particular the quarantined parent PicardTermwiseModelComparison remains a user.

## Where the brief, the DAG or earlier work was wrong

The item is not a fresh sorry obligation: coord/rework.tsv records a missing
quarantined module, and the preserved archive already contains its complete
mathematical proof. Restoring that proof and its original interface is the work
required here. No mathematical statement or DAG proof route needed correction.

The shorter-route search found Mathlib Iso.eq_inv_comp for the cancellation.
LeanFinder returned ordinary pullback-unit isomorphisms, which do not express the
pinned derived coherence. The existing canonical single comparison and composition
lemma give the direct route without new intermediate statements.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
