## What changed

Replaced the body of `WeilConjectures.IntegralFiniteExtension.scalarTensor_model_comparison`
with a proof from the flat K-flat representative normalization and the existing
`PurCompactSupport.scalarTensor_existsUnique`. The proof constructs the transported
natural tensor isomorphism, identifies it by uniqueness, and cancels the inverse
target adjoint comparison. The statement is unchanged.

Added `Sheaf.SixFunctors.IntegralHomTensorAdjointNaturality`. Its theorem
`tensorAdjointComparison_naturality` is proved from the existing
`IntegralHom.evaluation_naturality` and the canonical closed structure's evaluation
naturality. Four private categorical helpers derive parameter naturality of the
Hom equivalences and paste it with ordinary naturality of `leftAdjointUniq`.
`tensorAdjointComparison` explicitly assembles these components into a natural
isomorphism; it chooses no data from an existence statement.

Added `Sheaf.SixFunctors.IntegralHomScalarTensorRepresentativeComparison`.
`scalarTensorTransportOfSwap` and `scalarTensorTransport` are explicit whiskerings
and compositions of the specified isomorphisms. The remaining theorem states only
the normalization on flat-term K-flat complexes, before localization uniqueness
extends it to arbitrary derived objects. Each new node records the actual route.
No existing module besides the assigned item is changed.

Validation: all three modules compile through `lcompile.py` in import order;
the new modules took 12.5 s and 15.8 s, and the assigned module took 20.9 s.
No compiler warnings remain. The original declaration signature is unchanged,
and the three DAG Lean signatures match the delivered declarations.

## Proved and sorry left

The original hole in `WeilConjectures.IntegralFiniteExtension.scalarTensor_model_comparison`
is closed by a complete combining proof. The added theorem
`WeilConjectures.IntegralFiniteExtension.tensorAdjointComparison_naturality` is proved,
with zero local holes. Its proof uses the already stated evaluation-naturality
result; it does not repeat that result's representative calculation.

One new hole remains:
`WeilConjectures.IntegralFiniteExtension.scalarTensorTransport_normalization`, in
`Sheaf.SixFunctors.IntegralHomScalarTensorRepresentativeComparison`, node
`new-sf-integral-hom-scalar-tensor-representatives`. It is exactly `:= by sorry`,
with its source and proof in words. It asserts a representative square for actual
flat K-flat complexes, not the global scalar tensor comparison under another name.
The parent additionally proves two-variable naturality, invokes localization
uniqueness, and cancels the target comparison.

Counts: one original hole closed, one new hole added; net zero. This is a
**decomposition**, not a completed proof of the full dependency closure. All data
definitions are concrete, and no definition contains `sorry`.

## No longer needed

No mathematical dependency is pruned and no original public import is removed.
The parent's former representative-calculus dependencies move to the new
representative node; they remain needed there. The parent now directly uses the
two new nodes and the existing scalar tensor uniqueness node. Its new import is
proof-only. No unused trial helper is included in the delivery.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan left both the naturality of the
pointwise adjoint comparisons and the representative normalization as prose.
The existing `IntegralHom.evaluation_naturality` already supplies enough input to
prove the first part by categorical algebra. The scalar representative equation
remains the substantive outstanding calculation. The new statement includes all
original normalizations on t and e, and handles zero inputs and the empty scheme
through the same representative equation.

## New nodes

`new-sf-integral-hom-tensor-adjoint-naturality`, at
`dag/nodes/sec-six-functors/new-sf-integral-hom-tensor-adjoint-naturality.json`, records
the proved two-variable naturality and explicit tensor comparison. Its source is
the normalized adjunction argument of Stacks 08J9 and the finite-extension proof.
Searches found the Mathlib uniqueness-of-adjoints lemmas and the existing project
evaluation-naturality theorem, which the proof uses.

`new-sf-integral-hom-scalar-tensor-representatives`, at
`dag/nodes/sec-six-functors/new-sf-integral-hom-scalar-tensor-representatives.json`,
records the concrete transported tensor isomorphism and its flat K-flat
normalization. Its source is the representative part of paragraph 5 of the
finite-extension proof, Stacks Tags 06YY, 07A4 and 08J9. It does not assert equality
with the global `PurCompactSupport.scalarTensor`; that conclusion is proved in
the assigned module using the existing uniqueness theorem. No change record is
needed: no pre-existing statement, definition or interface is changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralHomScalarTensorModelComparison": "83cbecc03007676e23bcbe35ad3915abd48fc963", "Sheaf.SixFunctors.IntegralHomScalarTensorRepresentativeComparison": "5f9f53e50cb58f1f8e1aff307717102eb7d3d78d", "Sheaf.SixFunctors.IntegralHomTensorAdjointNaturality": "a559753713a66729c7210f72b8629cd0f162ff7b"}, "results": {}, "time": "2026-10-28T12:47:33+0800", "transitive": 0, "version": 1}
```

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
