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
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed in broken-tip snapshot | Forced proof adaptation: expose the local mate component before the existing rewrite. |

The added theorems have no existing external textual users. Existing callers keep
identical statements and definition bodies. The broken global build nevertheless
requires a proof-only adaptation in `ProperFlatOpenSquareMateIso` at line 190:
insert `change IsIso ((mateEquiv adjf adjf' (inv β)).app K)` before the existing
`rw [← secondMate_formula adjf adjf' adjgX adjg β K]`. The reported rewrite could
not find the mate component in `IsIso this✝¹`, whose local let is definitionally
that component; implicit-transparency checking also exposed a sheaf/K-flat type
mismatch. The explicit conversion exposes the component without changing any
statement, definition, visibility, docstring, import, or mathematical argument.
This theorem can be specialized to `schemeHomPullbackCounitIso` by the existing
original-counit normalization API. It does not assert that the old adjunction itself
is normalized, or that changing that adjunction alone preserves base-change mates.
No target's definition or meaning is changed.

## Status

landed 20261014T173546-L-2996755 2026-10-14 (merge of deliver/XRd4f549ddc0d8d578/Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso)

Repair prepared 2026-10-14 for the consumer failure at broken tip
7203881ce5a89cf381f49c8904a21439f3d8871f; pending independent reader.
