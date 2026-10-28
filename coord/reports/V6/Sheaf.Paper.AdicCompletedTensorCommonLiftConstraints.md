## What changed

The parent theorem now assembles the four constraint fields from four separately named
component theorems.  Each component theorem records the finite coefficient-field
representative calculation, native coherence transport, and independence under finite
extension that is required for that equation.  The sandbox compiles all five modules in
import order.

## Proved and sorry left

The parent declaration `completed_tensor_common_lift_constraints` is proved from the
four component declarations.  The following four strictly smaller component steps
remain `sorry` for later proof work:

- `completed_tensor_common_lift_constraints_associative`;
- `completed_tensor_common_lift_constraints_left_unit`;
- `completed_tensor_common_lift_constraints_right_unit`;
- `completed_tensor_common_lift_constraints_symmetric`.

Thus one parent hole was closed and four component holes were added.

## No longer needed

None.  The finite-model, tensor-unit, and native-coherence inputs remain needed by the
four component statements.

## Where the brief, the DAG or earlier work was wrong

The declared parent theorem quantifies over an arbitrary
`CompletedTensorCommonLiftTensorUnit` value.  Its `tensor` and `unit` fields are plain
isomorphisms, with no compatibility fields tying them to the supplied native
`RingedDerivedTensorCoherence`.  Therefore the native coherence data cannot by itself
prove the four displayed equations for an arbitrary `data`; a direct attempt to use
`Subsingleton.elim` fails because the relevant derived-category hom types have no
`Subsingleton` instances.  The component declarations preserve the exact parent
statement while isolating the missing finite-transport obligations for correction or
completion.

## New nodes

- `new-sf-adic-completed-tensor-common-lift-constraints-associative`;
- `new-sf-adic-completed-tensor-common-lift-constraints-left-unit`;
- `new-sf-adic-completed-tensor-common-lift-constraints-right-unit`;
- `new-sf-adic-completed-tensor-common-lift-constraints-symmetric`.

The component theorem conclusions are the individual fields of the parent structure,
so the parent proof uses each result directly in a structure literal rather than applying
a restated parent theorem.

Validation: `lcompile.py --all` compiled each component module and the parent module successfully.

The delivery packet contains only the assigned module, its four split modules, and their DAG records.

The packet was rechecked after the successful all-files compile before delivery.

The four new node records now include source citations, exact normalized Lean signatures,
three recorded search kinds, and the public-interface change record required by preflight.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": "0eca76ecbd74c77926bc1ebafe60cb4ed3e413b3", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsAssociative": "fb971b180453b4f3324489b28b7d44ceb4f5f374", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsLeftUnit": "73ef549699f142e4e7ce3af5e101fed5738a72ec", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit": "071c4890aa041501b4bbbf5d90346b8c02a287f9", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsSymmetric": "b3d3d362376566814d3cf608013cea110cb3c392"}, "results": {}, "time": "2026-10-28T08:16:51+0800", "transitive": 0, "version": 1}
```

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
