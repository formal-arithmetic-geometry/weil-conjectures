## What changed

`Sheaf.Paper.IntegralHomReducedEvaluation.reduced_evaluation_representative`
keeps its complete original signature. Its proof constructs the existential
isomorphism s by composing the scalar transpose of reduced evaluation with the
inverse of the transported signed Hom action. The equality follows by inverse
cancellation and the inverse law of the tensor-Hom adjunction. The isomorphism r
comes from a natural scalar tensor-resolution comparison and eI. The proved
`integralReduction_twoTerm_resolution` supplies the two-term coefficient object;
the two augmentations supply its derived identification with Q.

Four private proof imports were added: the three new modules listed below and
`Sheaf.Paper.IntegralReductionTwoTermResolution`. The original public import and
all existing declaration signatures remain unchanged. The original node's proof,
proof_deps and proof_origin now record this argument. No other existing module
or node was changed. Local irreducibility annotations prevent elaboration from
unfolding large tensor, Hom and scalar-derived constructions.

Validation: the main module compiles cleanly in 11.9 seconds with the default
heartbeat budget and without profiling or trace options. All three new modules
also compiled individually in import order. A traversal of the revised item's
580-node dependency closure found no cycle and no missing node.

## Proved and sorry left

This is a decomposition, not a complete proof from already proved results.
One existing hole was removed:
`WeilConjectures.IntegralHom.reduced_evaluation_representative`.
The proof combining the three new obligations is complete Lean. The item has
zero remaining holes. Three holes were added, each as an entire named theorem:

- `WeilConjectures.IntegralHom.reduction_tensor_resolution_comparison`
  (node `lem-sf-reduction-tensor-resolution-comparison`).
- `WeilConjectures.IntegralHom.perfectCoefficient_signedHomAction_isIso`
  (node `lem-sf-perfect-coefficient-signed-hom-action`).
- `WeilConjectures.IntegralHom.scalar_reduced_evaluation_transpose_isIso`
  (node `lem-sf-integral-hom-scalar-evaluation-invertible`).

Thus the packet closes one hole and adds three, a net increase of two holes.
Each new theorem has its exact signature in its node and a complete proof in
words in its docstring. There are no definitions containing sorry.

## No longer needed

No original imports were removed and no whole module or node is withdrawn.
The original node no longer directly lists these former proof dependencies:

- `lem-pc-kflat-resolution`: used inside the scalar-model and signed-action obligations.
- `lem-cbc-extension-tensor-comparison-independent` and
  `lem-pur-change-of-rings-tensor-cancellation-independent`: used inside the
  scalar-model obligation.
- `lem-weil-derived-scalar-extension-restriction-adjunction`: used inside the
  scalar-invertibility obligation and in the unchanged theorem statement.
- `lem-pur-rhom-well-defined-universes`: used inside the signed-action obligation.
- `def-coef-hom-representative-evaluation` and
  `lem-coef-hom-kflat-into-kinjective-independent-coefficients`: no explicit
  chain representative for testing maps or canonical evaluation square is
  needed in the main proof. The new invertibility lemmas use the existing
  derived Hom construction instead.
- `lem-sf-two-term-free-hom-tensor-components`: used inside the signed-action
  obligation and in the unchanged theorem statement's signed-map predicate.

These are removals from the main proof's direct dependency list, not claims
that all those nodes are globally unused. No globally pruned work is claimed.

## Where the brief, the DAG or earlier work was wrong

The original proof narrative prescribed a canonical s and a chain-level
evaluation identity. The statement only requires existence of s, allowing the
isomorphism-and-cancellation argument implemented here. This avoids assuming
naturality in K of the separately supplied adjunctions a.adjunction K, which
is not a field of TensorPresentation. No statement is marked disputed and no
hypothesis or conclusion has changed.

The new scalar-invertibility obligation overlaps the ultimate finite-coefficient
comparison assertion mathematically, but it is independent of the chosen
completed-ring representatives, signed chain map, and the equality sought here.
Its proof route is the exact two-term coefficient-cone argument, not an import
of `IntegralHomComparisonIsIso`, which would create a cycle through this item.
The signed-action obligation is purely about an arbitrary coefficient ring and
a perfect coefficient complex: it has no scalar reduction or evaluation data.
The scalar-model obligation has no internal Hom or evaluation data at all.
These are independent parts of the source's finite-free argument, not the
original representative-equality assertion under another name.

Edge cases checked mathematically include n=0 (the quotient uses the (n+1)-st
power), zero complexes, an empty scheme and a zero quotient. The signed-action
statement deliberately asserts invertibility only after composing with
homModelMap: it does not assert that I tensor an arbitrary K-flat Q is
K-injective or that the chain map f is itself an isomorphism.

## New nodes

`lem-sf-reduction-tensor-resolution-comparison`, in
`Sheaf.Paper.ReductionTensorResolutionComparison`, isolates the ordinary
extension-tensor cancellation and K-flat descent needed to construct r.
Its proof treats arbitrary complexes and does not involve internal Hom.

`lem-sf-perfect-coefficient-signed-hom-action`, in
`Sheaf.Paper.PerfectCoefficientSignedHomAction`, isolates the finite-coordinate
Hom calculation and transport along an isomorphism of K-flat coefficient
objects in the derived category. Only the composite into derived Hom is used.

`lem-sf-integral-hom-scalar-evaluation-invertible`, in
`Sheaf.Paper.IntegralHomScalarEvaluationInvertible`, isolates invertibility of
the scalar transpose using the two-term coefficient cone and exactness of
internal Hom in its second variable. No representative equality is required.

All three nodes keep the item's chapter and unit and cite the same current
blueprint source. There are no change records because no existing statement,
definition, instance, public import or attribute is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReducedEvaluation": "9ec837a93b48935a65eb840d1cd9e5d757e7ba20", "Sheaf.Paper.IntegralHomScalarEvaluationInvertible": "bb58c5171298d9d8afbcfed3e46a5f1a9c6e51f1", "Sheaf.Paper.PerfectCoefficientSignedHomAction": "00922460e1a70ada2e44472ed5082c8f91f9a707", "Sheaf.Paper.ReductionTensorResolutionComparison": "60076c86fa05b7434fafe1c4119477f684c5478a"}, "results": {"Sheaf.Paper.IntegralHomRepresentativeSquare": {"hash": "7457790233419ee3b3ed8326f13e84836f872b38", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T12:20:48+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
