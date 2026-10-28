## What changed

Added the proved heterogeneous normalization helpers
`normalizedProjectionPullbackTensor_heq`, `projectionTransportTensorComparison_heq`, and
`projectionPullbackTensor_heq`.  Split the remaining finite-stage cancellation into the
pointwise theorem `projectionTensorComparisonCompatible_component_of_representative_formula`
and used that theorem to prove the universally quantified
`projectionTensorComparisonCompatible_of_representative_formula` by introducing its two
inputs and applying the component theorem.  The component theorem is kept in the item
module to avoid an import cycle through the operation-coordinate definitions.

## Proved and sorry left

Proved `normalizedProjectionPullbackTensor_heq`,
`projectionTransportTensorComparison_heq`, `projectionPullbackTensor_heq`, and
`projectionTensorComparisonCompatible_of_representative_formula`.
The split theorem `projectionTensorComparisonCompatible_component_of_representative_formula`
retains one `sorry`; its node is
`lem-sf-common-projection-pullback-tensor-compatibility-component`.
The final theorem `commonProjectionPullbackTensorCompatibility` remains proved by the
bridge theorem and contains no `sorry`.

## No longer needed

None.  The operation normalization and representative declarations remain required by the
split component theorem.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the heterogeneous normalization bridge.  The missing
cancellation is a pointwise finite-stage obligation, so it was split into a strictly smaller
component theorem; the parent bridge now combines those components by a real `intro` and
application proof.  Direct rewriting of the original HEqs still requires dependent transports
through the rational and common tensor quotient objects, so the component theorem records that
remaining mathematical step for a follow-up worker.

## New nodes

`lem-sf-common-projection-pullback-tensor-compatibility-component` records the pointwise
finite-stage cancellation theorem and its representative-formula proof obligation.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.CommonProjectionPullbackTensorCompatibility": "a9f9424651cce3142bcc3e347021fe2f003631b9"}, "own_failed": ["Sheaf.Paper.CommonProjectionPullbackTensorCompatibility"], "results": {}, "time": "2026-10-28T09:13:55+0800", "transitive": 0, "version": 1}
```

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
