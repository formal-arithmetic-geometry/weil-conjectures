# AlgebraicGeometry.schemeHomDirectImageComparison_counit_transport

## Reason

The repair queue names the unnormalized legacy adjunction and tensor comparison.
The earlier original-counit API transports the tensorator, but had no proof that
simultaneously transporting the adjunction preserves the actual internal-Hom mate.
This delivery supplies that calculation, including arbitrary automorphism twists.
It is a proved enabling step and partial repair; the legacy repair remains open.

## Old

No counit-transport equation for the fixed direct-image internal-Hom comparison.
All existing definitions, statements, signatures and visibility are retained verbatim.

## New

Add `AlgebraicGeometry.internalHomMate_counit_transport` in the new module
`Sheaf.AlgebraicGeometry.InternalHomMateCounitTransport`. Add the proved scheme
specialization `AlgebraicGeometry.schemeHomDirectImageComparison_counit_transport`
and `AlgebraicGeometry.schemeHomPullbackAdjunction_counit_transport`
to the item's module, with a plain proof import of the generic theorem.
Their complete signatures are recorded in the delivered Lean and node records.
The SAME chosen comparison satisfies the old and the transported evaluation equations;
no new comparison object or existential choice is introduced.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | R2 | Uses the new generic transport theorem; existing declarations unchanged. |

The added theorems have no existing external textual users. Existing callers keep
identical statements and definition bodies, so no forced adaptation is necessary.
This theorem can be specialized to `schemeHomPullbackCounitIso` by the existing
original-counit normalization API. It does not assert that the old adjunction itself
is normalized, or that changing that adjunction alone preserves base-change mates.
No target's definition or meaning is changed.

## Status

landed 20261014T054722-L-2187349 2026-10-14 (merge of deliver/R2/Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso)
