## What changed

Filled `AlgebraicGeometry.Scheme.completedKoszulTensorQuotientAugmentation_unique` in
`Sheaf.Paper.CompletedKoszulTensorQuotientAugmentationUnique`. The statement and public
imports stay unchanged. Added the proof-only import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence` for the
proved scalar-extension unit isomorphism and its inverse section formula. Also added
`Sheaf.Paper.CompletedIntegralCoefficients` as a proof-only import, supplying the
coefficient-universe sheafification instances; the proof fixes their universe to t+1.

The private helpers prove the constant and completed degree-zero Koszul units invertible.
The constant-unit inverse follows the existing private argument in
`CompletedAdicKoszulKFlat` / `KoszulQuotientLimit`; scalar extension and its normalized
pure-tensor formula give the completed unit. The main proof uses Mathlib's
`HomologicalComplex.mapBifunctor.hom_ext`, cancels the invertible unit on the zero
summand, and uses the two vanishing hypotheses on every nonzero summand.

Updated the item's node to record these proof steps and the generic scalar-extension
unit tool. No unit route changes. No existing definition or statement changes.
The argument covers r=0 and zero coefficient rings without extra assumptions.

Validation: the complete module compiled through `lcompile.py` in 32.1 seconds,
with no errors or warnings. Its source statement is byte-for-byte unchanged, and
all Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.completedKoszulTensorQuotientAugmentation_unique`
(node `new-y2-completed-koszul-tensor-quotient-augmentation-unique`).

No holes added, no split-off statements, no sorry left in the delivered module.
Every private helper has a complete proof.

## No longer needed

None. No imports removed and no nodes or modules withdrawn. The existing summand
comparison plan is retained and completed; the construction/existence sibling remains
needed by its parent.

## Where the brief, the DAG or earlier work was wrong

The previous one-step proof description omitted the invertibility of the specified
degree-zero Koszul unit, which is necessary to cancel the normalization equation.
The delivery supplies that argument using the actual sheafification and scalar-extension
normalizations. The statement itself needs no repair.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
