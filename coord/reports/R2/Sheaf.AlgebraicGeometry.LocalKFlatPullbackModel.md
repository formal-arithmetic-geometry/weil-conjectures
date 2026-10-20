## What changed

Restored `Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel` from its quarantine
archive. Replaced the public import of the withdrawn Sheaf derived pullback with
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, and explicitly publicly
imported `Sheaf.Algebra.Homology.KFlat` to preserve the existing public predicate
and theorem signature. Recorded the definitional conversion from
`IsAcyclicTensorKFlat` to the source `IsKFlatTensor` before applying
`derivedPullback_spec`. The complete existing comparison proof is retained.
Updated only the node's proof-origin note; its attachment and dependencies stay.

Change record: `coord/changes/R2-local-kflat-pullback-restoration.md`.
Single-file compilation succeeds without warnings. Delivery preflight also checks
the declaration's axioms. No other module is adapted.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived module had zero sorries;
its restored module has zero sorries. Holes closed: zero. Holes added: zero.
`AlgebraicGeometry.derivedPullback_local_kFlat_model`
(node `lem-sc-local-kflat-pullback-model`) retains its complete proof and unchanged
signature. No intermediate result is split off.

## No longer needed

Removed the import of the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`.
Removed redundant private imports of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (publicly imported by the
retained source ExactFunctor module) and
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` (the weaker adjunction
used by the proof is already public in TensorPullback, imported by DerivedPullback).
No mathematical DAG dependency or parent is pruned. No module is withdrawn.
The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The source is absent because it was quarantined by the 2026-10-20 sync, not because
its mathematics was withdrawn. The archived import referred to the duplicate
Sheaf derived pullback. Its replacement import also needs the Sheaf K-flat
predicate explicitly; the adopted source names the identical predicate
`IsKFlatTensor`. Both definitions quantify acyclicity of the same total tensor
complex, so the existing public hypothesis supplies the source counit hypothesis
without changing the statement. Search found ordinary pullback APIs, but no
shorter local derived-model comparison. The original argument remains applicable.

`tools/downstream.py` cannot enumerate an absent quarantined module. Searches in
both live roots and quarantine find one direct archived consumer,
`AffineKFlatResiduePullbackModel`; its use of this theorem requires no adaptation.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
