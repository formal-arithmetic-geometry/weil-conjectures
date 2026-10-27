## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.adicResidue_finite_local_models` with a
proof from two smaller named obligations. The proof assembles the covering family,
transports the existing finite-projective completeness proof to the adic residue
presentation, preserves completeness on slices, and factors sieve arrows through the
family. Added the two strictly smaller intermediate statements
`adicResidue_finite_reduction_model_family` and `adicResidue_slice_completeness`, each with
its own node and documented source. The parent node proof route and dependencies were
updated to match the Lean proof.

## Proved and sorry left

This is a decomposition: one existing hole closed, two lower holes added (net -1),
not an axiom-free proof of the item. Closed the one sorry in
`AlgebraicGeometry.Scheme.adicResidue_finite_local_models`. Added two genuine lower-level
sorries: `adicResidue_finite_reduction_model_family` (covering family and finite reductions)
and `adicResidue_slice_completeness` (preservation of local derived completeness under an
arbitrary slice). Their nodes are `lem-sfb-adic-finite-reduction-model-family` and
`lem-sfb-adic-residue-slice-completeness`, respectively. The three private helpers
`adicResidue_complete_of_iso`, `adicResidue_constant_complete` and
`adicResidue_restriction_factor` have complete proofs.
No sorry occurs inside a definition.

## No longer needed

No imports or modules are pruned. The original finite-reduction, nilpotent-lissity,
stalk, tensor-pullback and algebraic inverse-limit nodes remain needed through
`lem-sfb-adic-finite-reduction-model-family`; completeness and slice-restriction
nodes remain needed through the reused proved model theorem and the new slice lemma.
The parent itself now cites only the family, slice lemma, existing perfect-model
completeness and exact restriction interfaces. This dependency regrouping does not
make the original mathematical obligations globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated completeness of the completed constant model and
preservation under slicing as one expanded argument. The library already contains the
complete finite-projective model argument (`AdicPerfectModel.complete_slice_model`), so
reusing it is shorter. The slice assertion is independent of boundedness and weak
contractibility and is therefore split as its own smaller statement. The weakly
contractible hypothesis remains only on V, as required by the target statement.

## New nodes

`lem-sfb-adic-finite-reduction-model-family` records the finite-reduction covering-family
obligation in `dag/nodes/sec-six-functors-basics/lem-sfb-adic-finite-reduction-model-family.json`.
`lem-sfb-adic-residue-slice-completeness` records the slice-completeness obligation in
`dag/nodes/sec-six-functors-basics/lem-sfb-adic-residue-slice-completeness.json`.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
