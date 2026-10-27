## What changed

Proved `Algebra.projective_of_geometricallyIntegral_fibres` without changing its signature,
public imports or hypotheses. Added five proved private helpers in the assigned module.
A field-valued map factors through the residue field of its prime kernel; the canonical
residue-field isomorphism gives the exact compatibility required by `hfibres`.
Affine tensor pullbacks give geometric integrality, including the algebraic fibres.
The declared Noetherian approximation theorem supplies a finite-type integer model.
The declared Noetherian projectivity theorem applies to that model, and the pushout
identifies the original algebra with its tensor base change. Projectivity ascends by
`Module.Projective.tensorProduct` and transfers through the resulting linear equivalence.
Canonical universe lifts retain the original independent universes and field quantifier.
Both scalar-action compatibilities are explicit in the tensor equivalence.

Updated the proof routes of both DAG nodes attached to this declaration. The unit route
is unchanged. No public signature changes, new modules or new nodes. The static interface check
requires a record for the declaration-scoped instance command:
`coord/changes/Z6-affine-projective-ulift-elaboration.md`. It documents the unchanged
consumer interface and every downstream module.

## Proved and sorry left

Closed 1 hole: `Algebra.projective_of_geometricallyIntegral_fibres`, attached to
`lem-trf-affine-geometrically-integral-projective` and
`lem-trf-local-fibres-integral-projective`.
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses the already declared approximation and Noetherian projectivity theorems;
those existing dependencies are not claimed as proved by this delivery.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.FunctionField`: no function-field
argument is needed, only integrality of a domain's affine spectrum. The corresponding
DAG leaf remains needed for its integral-spectrum clause. Removed the purported proof
dependency from `lem-trf-affine-geometrically-integral-projective` to
`lem-trf-local-fibres-integral-projective`: both attach to the same Lean theorem.
The alias node remains attached and its actual approximation route is retained.
No dependency module is withdrawn; no other mathematical dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The affine node's step 2 proposes applying the local-fibres node as an existing theorem,
but the stage-2 alias repair attached both nodes to this same declaration. That would be
circular in Lean. Implemented the local-fibres node's three-step approximation plan
instead, using its existing dependency statements. The declaration docstring, delivered
node proofs and private helper now describe the actual approximation route explicitly. No statement correction was needed.

Searches run through msearch: LeanFinder for the algebra-projectivity assertion, Loogle
for `Module.Projective, Algebra.FinitePresentation`, and grep for geometric-integrality
and fibre projectivity. The results offer only module finite-presentation criteria,
which cannot replace finite presentation as an algebra. Read Stacks `flat.tex`,
Tag 05FT, its Noetherian approximation paragraph, and the current blueprint unit.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
