## What changed

Completed the listed retirement of `Sheaf.AlgebraicGeometry.SmoothStageAffineModel`.
Removed the copy through `deleted.txt`; the delivery tool installs an empty module.
Reattached `lem-sbc-noetherian-approximation-smooth-stage-affine-model` to the proved
`WeilConjectures.AlgebraicGeometry.SmoothStageAffineModel` declaration with the same name,
and aligned its statement and proof with that declaration's canonical pullback conclusion.

Change record: `coord/changes/H8-retire-smooth-stage-affine-model.md`.

## Proved and sorry left

This is a retirement repair with zero original holes. Closed: 0. Added: 0. Split off: 0.
No `sorry` remains in the withdrawn item and no holes are introduced elsewhere.
The official `AlgebraicGeometry.Scheme.NoetherianApproximation.exists_smooth_affine_model`
is already proved. Its axiom check returns only `propext`, `Classical.choice`, `Quot.sound`.
A separate sandbox check derives the exact former existential-model conclusion from
that official theorem, using the canonical pullback and identity isomorphism; it has
only the same permitted axioms. These checks do not count as newly closed holes. The unchanged official consumer
`WeilConjectures.AlgebraicGeometry.NoetherianApproximationSmoothStage` was also
compiled separately from a sandbox copy (2.7 seconds, no warnings).

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.SmoothStageAffineModel`.
Its old imports disappear with the copy:
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`WeilConjectures.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`, and
`WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent`.
These imported modules are retained: the official proof still needs its dependencies.
No mathematical dependency node or unit step is pruned; the item node retains
`lem-sbc-affine-limit-smooth-stage` as its proof dependency.

The fresh source/quarantine import scan and `tools/downstream.py` both find zero
consumers of the copy. No current DAG parent (including proof-step uses) or unit
realization points to its node. The historical consumer named in the retirement row
has already migrated to the official module. No consumer adaptation is needed.
The official module's import closure contains no Sheaf/upstream twin clash.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but the actual assignment is a listed
retirement with zero holes. The old DAG attachment still named the unused Sheaf copy.
The official theorem asserts smoothness of the canonical second projection; the old
copy merely supplied a smooth morphism on an abstractly isomorphic source without a
base-compatibility equation. The updated node records the official stronger statement
and its exact signature. There are zero current DAG citers to adapt. The compiled
implication to the previous conclusion confirms no old mathematical consequence is lost.
The source is Stacks Tag 0C0C, `limits.tex`, `lemma-descend-smooth`, read locally.
The node's `statement_change.by` uses the legacy `H8 stage 2` syntax required by the
shared correction-record validator; this delivery is stage 3.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
