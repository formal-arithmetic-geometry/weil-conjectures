## What changed

Added two named intermediate theorem interfaces and proved the assigned theorem
`completed_tensor_common_lift_coherence` by assembling them. The tensor/unit interface
isolates construction of the common-stage tensorator and coefficient unit. The constraint
interface isolates transport of associativity, both unit equations, and symmetry from finite
normalized representatives. The assigned module imports the constraint interface and builds
`CompletedTensorCommonLiftCoherence` by explicit structure construction.

## Proved and sorry left

The original theorem `completed_tensor_common_lift_coherence` is proved. Two strictly
smaller theorem holes remain:

- `completed_tensor_common_lift_tensor_unit` in
  `Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit`.
- `completed_tensor_common_lift_constraints` in
  `Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints`.

They are represented by the two new DAG nodes below. No definition contains `sorry`.

## No longer needed

No imports were removed. The assigned theorem uses the two new interfaces; the finite-model,
native-realization, and native coherence dependencies remain needed by those interfaces.

## Where the brief, the DAG or earlier work was wrong

The original node bundled finite common-stage descent and all four coherence diagrams into
one proof hole. The available declarations do not expose a single theorem performing that
construction. Naming the tensor/unit construction and the constraint transport gives two
strictly smaller interfaces, while the assigned theorem is a complete categorical assembly
from them.

## New nodes

- `new-sf-adic-completed-tensor-common-lift-tensor-unit`, stated in
  `Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit`.
- `new-sf-adic-completed-tensor-common-lift-constraints`, stated in
  `Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence": "523461ecea308f1db359bf790e1d071c1c14bfb2", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": "3721c05e113511bafe30312ae0a60b45b9ec367d", "Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit": "8e0f78f81fada3d58fc7e50dc66cb0eac2b63409"}, "results": {}, "time": "2026-10-28T05:09:18+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
