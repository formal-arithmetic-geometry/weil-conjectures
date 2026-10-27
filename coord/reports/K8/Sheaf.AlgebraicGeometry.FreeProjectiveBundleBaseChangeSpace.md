## What changed

Proved `AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace`
in `Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace`. Existing public definitions,
statement, universes and public imports are unchanged. All additional helpers are private and
proved in the item module. No other existing module is changed.

The proof constructs the graded integral polynomial map, proves its homogeneous span and
irrelevant-ideal conditions, and applies the declared affine Proj scalar-extension theorem with
Mathlib's polynomial tensor-product equivalence. Naturality of the sheaf inclusions proves
coordinate restriction; polynomial extensionality proves coefficientwise restriction.
Compatible cartesian charts feed the source library's `relProjIsoOfIsPullback`; its chart equation
and the relative-Proj colimit prove normalization and uniqueness. The DAG proof now records this
route. This is the existing affine construction and gluing argument, with the gluing and inverse
construction supplied by the declared relative-Proj universal property.

Added the proof import `Mathlib.RingTheory.TensorProduct.MvPolynomial`. Retained the proof imports
`Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension` and
`WeilConjectures.AlgebraicGeometry.RelativeProj.Universal`.

Validation before import cleanup: the complete file compiled without errors or warnings through
`lcompile.py` in 16.2 seconds. Delivery repeats compilation after cleanup. Read Stacks
`constructions.tex`, definition-projective-space and its following paragraph (01NF), and
lemma-relative-proj-base-change (01O3). Checked the existing affine scalar-extension signature and
relative-Proj universal property. The argument includes r = 0, the empty base, zero affine rings,
and arbitrary nonseparated bases: no point or nonzero coefficient is selected, and the existing
locally directed affine-chart colimit handles intersections.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace`
(node `lem-trf-free-projective-bundle-base-change-space`). Added 0 holes and split off 0 statements.
The delivered item has 0 textual `sorry`. Existing dependencies retain their own proof status;
this is a proof from the project's declared dependencies, not a claim that their entire closure
is already axiom-free.

## No longer needed

Removed these direct proof imports:
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`;
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`;
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` (replaced with the tensor-product import);
- `Mathlib.AlgebraicGeometry.Gluing`.

Removed these direct proof dependencies and their obsolete tool-use approvals:
`lem-weil-pbc-quasi-coherent-symmetric-algebra`,
`lem-weil-pbc-symmetric-algebra-free-module-polynomial`,
`lem-weil-pbc-symmetric-algebra-graded`,
`lem-weil-pbc-scheme-morphism-gluing`, and `lem-weil-pbc-affine-opens-basis`.
The first three inputs have already been incorporated into the canonical polynomial interface
of `RelativeProjectiveSpace`. The latter two operations are supplied by the already declared
relative-Proj universal property. Also removed the direct proof dependency
`def-weil-open-immersion`: cartesian affine charts suffice as the universal property's input.
The proof instead explicitly depends on `def-nagata-relative-projective-space` for its proved
polynomial interface. No module is withdrawn and no transitive dependency used by another
module is claimed unnecessary. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original node proposed rebuilding
scheme gluing and gluing inverse maps. The current source library already proves the requisite
chart characterization as `relProjIsoOfIsPullback`, so the delivery uses that existing declaration.
The local polynomial grading and equivalence are also already available. Only the item's proof
route and its dependency/tool-use lists are updated; its natural-language statement and Lean
attachment stay unchanged. No new nodes and no change records are needed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
