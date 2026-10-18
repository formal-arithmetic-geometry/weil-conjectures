## What changed

Proved `AlgebraicGeometry.Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields`
in `Sheaf.AlgebraicGeometry.SteinFiniteFibresResidueFields`, with its signature unchanged.
The proof follows all six planned steps: integral incomparability gives a T1 target fibre;
the Noetherian source fibre has finitely many dense component generic points; its continuous
surjection onto the target fibre gives finiteness; a closed lift of each target point has
finite residue extension; the compatible field tower gives the desired subextension.

Reused `Scheme.Hom.finite_residueField_of_isClosed` and
`Scheme.Hom.specMap_residueFieldAlgebraMap` from `WeilConjectures.PointCount`.
Added its proof-only import and `Mathlib.FieldTheory.Tower`. The private proved helper
`finite_left_of_comp` applies `Module.Finite.left` to field maps with their induced algebras.
The residue-field comparison explicitly uses the pullback equation, naturality of field-valued
points, cancellation of `fromSpecResidueField`, and faithfulness of `Spec`.
Updated the node's proof text and proof origin to describe these implementations.

Validation: `deliver3.py --no-push` passed compilation, the per-declaration axiom probe,
and stage-3 preflight (dry-run commit `9ebe1e0b25`; review class CODEX for the node update).

All writes are confined to this sandbox. No definitions, public signatures, or target
statements changed. The empty source/fibre cases require no chosen point: the finite-image
argument handles them, and a closed point is chosen only for an existing point of the target.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.steinFactorizationBase_finite_fibres_residueFields`
(node `lem-weil-pbc-stein-finite-fibres-residue-fields`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.
The proof uses the existing Stein factorization declaration as authorized by the brief.

## No longer needed

Removed the unused proof-only import `Mathlib.RingTheory.Jacobson.Ring`.
The closed-point finite-residue assertion is reused from `WeilConjectures.PointCount`,
so a separate affine-neighbourhood/Zariski-lemma implementation is unnecessary here.
No DAG dependency node or project module is pruned: the six-step mathematical route and
all its dependencies remain, with the existing source-library theorem implementing step 5.
The unit's realized statement and proof steps are untouched.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original plan was valid. The source library already
contains the finite-residue-field theorem needed at step 5, which avoids reconstructing
its affine-chart proof. The first compiler request failed with no answer from the server;
a retry reached Lean successfully. No tool was modified or bypassed.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
