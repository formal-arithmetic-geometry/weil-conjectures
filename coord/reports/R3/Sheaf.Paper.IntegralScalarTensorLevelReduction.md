## What changed

Proved `WeilConjectures.integralScalarTensorLevelReduction` in
`Sheaf.Paper.IntegralScalarTensorLevelReduction`, preserving its recorded signature.
The assigned source was absent from the shared checkout, with no matching rework or
quarantine entry; its exact theorem statement was restored from the existing DAG
Lean record. The current claim names R3, and there is no current return for this item.

The proof uses the ordinary scalar adjunction, the existing generator-normalized
finite tensor comparison, and the existing total tensor extensionality helper.
Three proved private helpers lift finite coefficients, move a lifted coefficient
through a balanced tensor, and establish finite tensor extensionality on original
input sections. The final square follows from the supplied normalization at both
levels and the recorded transition formulas. Only the assigned module and its
node are changed. No definitions, shared instances or other modules are changed.

## Proved and sorry left

Closed 1 of 1 assigned holes:
`WeilConjectures.integralScalarTensorLevelReduction`
(node `lem-pur-integral-scalar-tensor-level-reduction`).

There are zero remaining textual `sorry` proofs in the delivered module and zero
new holes. Nothing is split off. The private helpers `projection_surjective`,
`reduction_tensor_lift`, and `finite_tensor_ext` are fully proved.
Existing imported obligations remain assigned to their own modules. The final module compiled cleanly
with `lcompile.py` in 15.4 seconds, with no compiler warnings. No flatness, boundedness,
nonempty-scheme, or nonzero finite-coefficient assumption was added; the argument
also covers n = 0 and identity coefficient extension.

## No longer needed

No modules are pruned and no original imports are removed. The direct proof edge
to `lem-pur-sheaf-ring-derived-coefficient-adjunction` is unnecessary: the existing
ordinary scalar adjunction and total tensor extensionality helpers implement that
part of the argument. Its module remains a transitive dependency of those helpers;
this is not a claim of global pruning. All other original proof dependencies are
retained. The proof does not import the parent `IntegralOperationsScalarComparisons`
and does not use tower existence or uniqueness to prove its own lower obligation.

## Where the brief, the DAG or earlier work was wrong

The shared checkout lacked the assigned Lean source although its DAG Lean record
and R3 claim were present. The declaration was reconstructed verbatim from that
record; no mathematical statement was changed and no quarantine was withdrawn.

The proof plan is valid. Its generator-extensionality step can reuse existing
proved helpers in `IntegralTensorReductionTowerComparison` and
`IntegralTensorTransitionCompatibility`. Constant quotient surjectivity from
`CompletedIntegralFiniteQuotientHomExt`, followed by the constant-to-completed
map, lifts each finite coefficient on the same object. This avoids a new local
lifting or tensor generation obligation. The node's proof and dependencies now
record the actual argument. The unit route is preserved.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
