## What changed

Marked the assigned theorem `completed_tensor_common_lift_constraints_associative` as
`STATEMENT-DISPUTED` and retained its exact signature and `sorry`. The field
`CompletedTensorCommonLiftTensorUnit.tensor` is an arbitrary natural isomorphism;
no hypothesis relates it to `N`, `coherence.associator_model`, or the finite
representative equations.

## Proved and sorry left

No holes were closed. The existing `sorry` in
`completed_tensor_common_lift_constraints_associative` remains, under node
`new-sf-adic-completed-tensor-common-lift-constraints-associative`.

## No longer needed

None. The imports are required to state the existing declaration and its data.

## Where the brief, the DAG or earlier work was wrong

The theorem is underdetermined as written. `CompletedTensorCommonLiftTensorUnit`
contains only `tensor` and `unit` isomorphisms. Since `data.tensor` is quantified
arbitrarily, native coherence and finite-model hypotheses cannot imply the
associativity equation for it. The proof plan's finite representative transport
would apply only after adding a compatibility equation identifying the supplied
natural isomorphism with those representatives (or restricting `data` to the
canonical construction). This is the same interface defect recorded by the
previous split delivery; the statement should be repaired before a proof is
attempted.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsAssociative": "8afe7723a23d219cb3f28904f6db52a5c46f1551"}, "results": {}, "time": "2026-10-28T10:36:22+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
