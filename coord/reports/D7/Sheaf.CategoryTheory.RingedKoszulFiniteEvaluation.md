## What changed

Proved `CategoryTheory.exists_ringedKoszul_finiteEvaluation` without changing its statement.
The proof constructs the canonical evaluation in the direction from the strict tensor tower
to the Hom tower, assembles a natural isomorphism, and takes its inverse. Coefficient
naturality and compatibility with the specified unit follow by cancellation against evaluation.

Added three supporting modules. `RingedComplexTensorEvaluation` transports the existing
cochain tensor-Hom adjunction to the project's signed product Hom, identifies its source
functoriality, and proves naturality, invertibility for dualizable sources, and the tensor-Hom
unit identity. `RingedKoszulDualizable` proves dualizability by bounded two-term factors and
induction on the actual recursive Koszul diagram. `RingedHomTensorUnitNormalization`
identifies the adjunction unit with inverse evaluation at one, including the sheafification
and degree-zero unit-complex identifications.

The item adds only private proof imports. No existing definition, statement, attribute,
public import, source-library module, or consumer is changed.

## Proved and sorry left

Closed the one original hole, `CategoryTheory.exists_ringedKoszul_finiteEvaluation`.
Added no holes. All supporting statements and definitions are proved or explicitly constructed.
The proof reuses the already proved bounded-complex duality theorem,
`MonoidalClosed.isIso_ihomUnitTensorToIhom`, and the signed ordinary-Hom/internalHom comparison.

The new proved declarations are `ringedComplexCurry_component`,
`ringedComplexTensorEvaluation_naturality`, `ringedComplexTensorEvaluation_isIso`,
`ringedComplexTensorEvaluation_source`, `ringedComplexTensorEvaluation_unit`, `ringedComplexHomUnit_eq_curry`,
`ringedKoszulStage_dualizable`, and `ringedComplexHomUnit_eq`, in namespace `CategoryTheory`.
No `sorry` remains in the delivery.

## No longer needed

No original import, declared dependency, node, or module is pruned: the two original
definition dependencies remain necessary. The original degreewise finite-direct-sum
calculation is replaced by the already proved bounded-complex duality and closed-category
evaluation API. This avoids introducing new degreewise evaluation or finite-support lemmas.
Temporary proof-development imports were removed or made private where appropriate.

## Where the brief, the DAG or earlier work was wrong

The statement and its edge cases are valid unchanged. The current latest blueprint unit
and the completed-pullback reduction formula retain the completion-map convention used here.
The supporting nodes retain the parent's historical ancestor id and identify its corresponding
place in the current latest blueprint. The DAG's proof plan did not exploit
the project's existing bounded-complex dualizability and canonical closed-category evaluation
theorems. The ordinary Hom and upstream cochain internalHom use different differential signs;
transporting the adjunction uses the proved degreewise sign comparison rather than identifying
the two definitions directly. The empty Koszul family uses unit duality, and the argument
requires no division, regularity, or restriction on zero or invertible generators.

## New nodes

`lem-weil-pbc-ringed-complex-tensor-evaluation` records the transported adjunction and the
canonical evaluation with its naturality, dualizable-source invertibility, and unit law.
Its Lean module is `Sheaf.CategoryTheory.RingedComplexTensorEvaluation`.

`lem-weil-pbc-ringed-koszul-dualizable` records dualizability of the actual finite Koszul
stages. Its Lean module is `Sheaf.CategoryTheory.RingedKoszulDualizable`.

`lem-weil-pbc-ringed-hom-tensor-unit-normalization` records the identification of the
adjunction unit with inverse evaluation at one. Its Lean module is
`Sheaf.CategoryTheory.RingedHomTensorUnitNormalization`.

The original node's proof, proof dependencies and proof origin now describe this route.
No change record is needed because no existing interface changes.

The normalization helpers use local instance parameters for the already available
sheafification properties. This avoids repeatedly reconstructing those instances
while checking the concrete unit calculation, and keeps the module below the
per-file compile limit.

Validation: `lcompile.py --all` accepted all four modules without warnings.
The assigned module compiled in 11.2 seconds; the unit normalization compiled
in 48.7 seconds, within the 60-second limit. The original theorem statement
is byte-for-byte unchanged. The delivery contains zero `sorry` tokens.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
