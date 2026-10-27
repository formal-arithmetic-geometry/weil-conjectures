## What changed

Restored lean/Sheaf/AlgebraicGeometry/DiagonalBaseChangeUpperShriek.lean from its exact
quarantine path in coord/rework.tsv. Replaced the retired public DerivedPullback import
with WeilConjectures.AlgebraicGeometry.DerivedPullback, preserving the theorem signature.
Replaced the ordinary structure-sheaf proof import with the existing derived version.

The proof applies proper_flat_rightAdjoint_baseChange to the self-product at O_S[0].
It lifts nonempty_derivedPullback_structureSheaf_iso to D_QCoh(X), applies b.mapIso,
and composes the inverse isomorphisms. Proof irrelevance reconciles the supplied QCoh
preservation witnesses. No hypotheses, definitions, source modules or target statements change.
The item's DAG proof now names the existing derived structure-sheaf lemma actually used.
The first server compile completed in 6.7 seconds; its only warning was the style
suggestion to replace haveI by have for the IsIso proof, applied before delivery.
Change record: coord/changes/C2-diagonal-basechange-restoration.md.

## Proved and sorry left

Closed the one existing hole: AlgebraicGeometry.diagonal_baseChange_upperShriek
(node lem-sc-smooth-proper-diagonal-basechange-upper-shriek).
No sorry remains in the restored module; no holes or new declarations are added.
The proof uses the existing general base-change theorem and existing derived unit theorem.

## No longer needed

Removed public import Sheaf.AlgebraicGeometry.DerivedPullback: it is withdrawn and empty;
the defining source module supplies the same derivedPullback declaration.
Removed direct proof import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
and direct proof dependency lem-weil-pbc-module-pullback-structure-sheaf in favor of
WeilConjectures.AlgebraicGeometry.DerivedPullbackStructureSheaf and
lem-sc-derived-pullback-structure-sheaf-local. The ordinary unit theorem remains a
transitive dependency of the derived theorem, so its module and node are not pruned.
No modules or nodes are withdrawn; the unit route and quarantined parents remain intact.

## Where the brief, the DAG or earlier work was wrong

The missing file is a quarantine repair, not a withdrawal. Its rework row records the
private-import visibility error. The statement needs a direct public import of the
current derivedPullback module. The original DAG's second step uses the ordinary
structure-sheaf pullback lemma as though it already computed derived pullback. The
existing derived structure-sheaf lemma supplies that computation without a new split.

Read the current blueprint finite-duality proof and Stacks duality.tex,
lemma-proper-flat-base-change and lemma-smooth-proper. The current smooth-proper proof's
third displayed equality uses pr₁ ∘ Δ = id; the archived docstring's third-equality
citation is historical. The relevant theorem here is exactly Tag 0AAB specialized
to the self-product. No change to the unit's route is needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
