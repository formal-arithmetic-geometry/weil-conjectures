## What changed

Marked `completed_tensor_common_lift_agreement_component` as
`STATEMENT-DISPUTED` in the item module.  The module still compiles with its
original `sorry`; no declaration or import interface was changed.

## Proved and sorry left

No holes were closed (0 of 1).  No holes were added.  The existing
`completed_tensor_common_lift_agreement_component` remains `sorry`, with node
`lem-sf-adic-completed-tensor-common-lift-agreement-component`.

## No longer needed

None.  The existing `AdicCompletedTensorCommonLiftCoherence` import and all
declared dependencies remain necessary for the disputed statement.

## Where the brief, the DAG or earlier work was wrong

`CompletedTensorCommonLiftCoherence` contains a tensor isomorphism, a unit
isomorphism, and the four monoidal constraint equations, but it contains no
equation relating its tensor component to the finite model `N`.  The theorem
quantifies over an arbitrary value `C` of this structure and then claims that
its tensor component is the finite normalized composite determined by `N`.
The only available structure carrying that equation is
`CompletedTensorCommonLift`, whose `integral_tensor` field already has the
claimed conclusion; it is defined in a downstream module and cannot be used
here without an import cycle.

The defect is substantive: transporting a coherent tensorator by a natural
automorphism of the ordinary realization (for example the scalar `-1`
automorphism in a nonzero derived module category, with the corresponding
transport of the unit and constraints) produces another coherent lift, while
the finite composite fixed by `N` is unchanged.  Thus the displayed equality
cannot follow from the current hypotheses.  A valid repair must either add the
finite normalization field to the coherence input or change the theorem to
take a `CompletedTensorCommonLift` (or an equivalent normalized lift).

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftAgreementComponent": "ef8353b61577b32093d916c37d2019239ac4d85e"}, "results": {}, "time": "2026-10-28T08:15:43+0800", "transitive": 0, "version": 1}
```

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
