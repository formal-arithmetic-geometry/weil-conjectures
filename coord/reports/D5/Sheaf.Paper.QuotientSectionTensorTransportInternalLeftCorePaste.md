## What changed

Filled `section_tensor_transport_internal_left_paste` in
`Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCorePaste` by a direct
naturality and cancellation proof. Statements, definitions and public imports are
unchanged. Added a private proof import of `IntegralResidueDerivedMonoidal` to
expose the existing internal monoidal instances. Added the fully proved private
`paste_output_computation` to perform the final reassociation in an abstract
category, keeping the large derived constructions out of those rewrites. Updated the item's node to record
the scalar normalization and output tensor normalization actually used.

The proof first moves the input localization maps across barB, cancels the inverse
scalar comparisons in TensorSectionCondition, and substitutes the scalar
normalization separately on P and Q. Naturality of output qTensor moves the
ordinary comparison maps to the final total. Output representative normalization
and tensorComparison naturality cancel all remaining comparison isomorphisms.
Functoriality and hbn finish the equality with scalarTensorSectionPath.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_internal_left_paste`
(node `lem-sfb-quotient-section-tensor-transport-internal-left-paste`).
No holes added or split off; no sorry remains in the delivered module.
The final single-file server compile passed without warnings in 55.3 seconds.
A source comparison confirms that the complete original theorem statement is
unchanged. There are no profiling options or lines exceeding 100 characters.

## No longer needed

No imports, modules or nodes are withdrawn. The direct proof does not use the
supplied hcn and hqnorm equations, or hb separately from its already supplied
instance hbn. It uses hc on P and Q, rather than normalizing the input qTensor or
the scalar comparison on P tensor Q. Their binders are retained unchanged for
compatibility. Both original definition dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

The old plan suggested substituting all three supplied normalization equations.
The direct output-side paste needs only hbn of those three; the other identities
follow a different, unnecessary route. No statement correction is required. The
item's existing docstring carries its parent's core blueprint tag; the actual
Lean attachment is the paste node recorded above.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCorePaste": "502a861c160f5d34304fd889dbaec616752c528f"}, "own_failed": ["Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCorePaste"], "results": {}, "time": "2026-10-28T12:19:08+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
