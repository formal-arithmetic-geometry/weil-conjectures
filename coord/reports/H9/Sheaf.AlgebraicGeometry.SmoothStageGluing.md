## What changed

Withdrew the unused Sheaf.AlgebraicGeometry.SmoothStageGluing twin via deleted.txt.
Reattached lem-sbc-noetherian-approximation-smooth-stage-gluing to the existing proved
WeilConjectures.AlgebraicGeometry.SmoothStageGluing declaration, recording its exact
signature and its actual transport proof. No WeilConjectures file is changed.
Change record: coord/changes/H9-smooth-stage-gluing-retire-twin.md.

The current parent already obtains a smooth canonical pullback stage, and applies
the upstream gluing theorem with that projection, Iso.refl and Category.id_comp.
This actual replacement argument remains in the library. There are zero Lean or
quarantine importers of the withdrawn module, zero DAG dependency parents of its
node, and no unit realized statement or proof step requires this module.

Validation: the original assigned module compiled cleanly through lcompile.py.
A separate scratch module importing the upstream gluing module and its active
parent compiled cleanly. #print axioms for both smooth_stage_of_affine_models and
exists_smooth_stage reports exactly propext, Classical.choice and Quot.sound.

## Proved and sorry left

Original local holes: 0. Holes closed: 0. Holes added: 0. Holes split off: 0.
No sorry remains or is added by this packet. The already proved declaration
AlgebraicGeometry.Scheme.NoetherianApproximation.smooth_stage_of_affine_models
is retained in its upstream module; the inactive Sheaf version is withdrawn.
The active parent's exists_smooth_stage also has no sorryAx dependency.
This is duplicate-module pruning and attachment reconciliation, not a new proof.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.SmoothStageGluing.
Its imports are removed with it: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit,
WeilConjectures.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage, and
WeilConjectures.RingTheory.SmoothAlgebraFilteredColimitDescent.
The gluing node no longer depends on lem-sbc-affine-limit-smooth-stage: transport
along a specified base isomorphism only uses def-sbc-smooth-morphisms. The general
affine-limit theorem and its algebra descent dependencies remain needed by the
active affine-model construction; their modules and declarations are preserved.
The gluing node itself is preserved and attached to its upstream realization.

## Where the brief, the DAG or earlier work was wrong

The assigned module has zero holes and no current return, repair, or rework entry.
Its proof had already been completed, while its node's Lean attachment still named
the unused Sheaf twin. The active upstream parent uses the upstream version.
The old hmodel only asserts a scheme isomorphism and does not compare q with the
projection over the base; the old proof correctly relies on its separate smooth
limit data instead. The existing upstream gluing interface includes precisely the
missing base compatibility. No target, unit, source signature or definition changes.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
