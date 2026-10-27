## What changed

Implemented `AlgebraicGeometry.Scheme.completedKoszulUnitTensorRealization` by the
actual inverse left unitor and a fixed automorphism of the single cochain tensor
unit. The automorphism is determined by the supplied `c` and the normalized
scalar-unit isomorphism on the regular coefficient module. Its action is the
same at every level.

Private proved helpers identify the normalized unit as invertible, compute every
successor composite on exterior generators, and verify the unitor cancellation
at degree zero. The constant-unit and scalar-extension arguments reuse the proved
private arguments in `CompletedKoszulTensorQuotientAugmentationUnique`; they are
included here because those private names cannot be imported. Scalar-unit
invertibility is constructed directly by the local tensor multiplication
isomorphism and sheafification, following the analogous construction in
`FlatConstantTensorProZeroCones`. The new module imports
`CompletedIntegralCoefficients` and the Mathlib tensor tower API for its proofs; the item imports the proved normalization module.

Updated the item's DAG proof to these steps. The existing theorem statement,
definitions, public imports, and module interface are preserved. There are no
changes to other existing modules or nodes. A new fully proved module,
`Sheaf.Paper.CompletedKoszulRegularUnitNormalization`, contains the scalar-unit
construction and normalization. This keeps each compilation below the per-file
limit and exposes only an existence theorem whose witness is explicitly constructed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.completedKoszulUnitTensorRealization`, node
`lem-weil-pbc-completed-koszul-unit-tensor-realization`.

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No statements with holes were split off. The new helper theorem
`AlgebraicGeometry.Scheme.completedKoszulRegularUnitNormalization` is also proved.
Every private helper is proved; both modules contain zero holes.

Standalone server compilation (`lcompile.py --all`) passes without warnings:
28.0 seconds for the new normalization module and 45.6 seconds for the item.
The delivery tool additionally checks axioms and interfaces.

## No longer needed

No modules or declarations are withdrawn, and no imports are removed.
The theorem `completedKoszulTensorQuotientAugmentation` is not used as a proof
premise, so its node is removed from the item's `proof_deps`. Its public import
is retained: it supplies the actual tower data used in the statement and
preserves the existing importer interface. Consequently this is not a claim
that its module has left the targets' import closure.

No finite quotient realization, augmentation existence, cone comparison,
pro-zero argument, or derived inverse-limit theorem is needed in this proof.
The unit's blueprint route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned scalar-section adjustment can be
implemented categorically by tensoring an automorphism of the tensor unit.
The supplied transitions need not satisfy separate coherence hypotheses:
their component formula identifies them with all composites of the recorded
successors. Rank zero, equal indices, zero rings, and the empty scheme require
no extra hypotheses.

Searches run through `msearch.py`: LeanFinder for natural action of tensor-unit
automorphisms found generic monoidal APIs; Loogle for
`MonoidalCategory.leftUnitor` returned an unknown-identifier/no-hit result;
grep for Koszul realization isomorphisms returned no service hit. Local `rg`
found the existing normalized-unit proof and the successor-composite
calculation in `NilpotentKoszulGradedTower`.

## New nodes

`lem-weil-pbc-completed-koszul-regular-unit-normalization`, in
`Sheaf.Paper.CompletedKoszulRegularUnitNormalization`, is a fully proved
coefficient-module normalization. It constructs one regular-unit isomorphism
and proves its prescribed value in degree zero at every Koszul level. It has no
complex tensor comparison or tower-naturality conclusion, and introduces no
statement with a hole. It is extracted to reduce checking time after the combined
file exceeded 60 seconds. No change record is needed: no existing public
statement or definition is changed.

Blueprint search for scalar units found only an unrelated finite compact-support
comparison. The ancestor helper did not resolve the generated item; the new
node follows the explicit existing `blueprint.from` chain to
`prop-weil-pbc-koszul-reconstruction`.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
