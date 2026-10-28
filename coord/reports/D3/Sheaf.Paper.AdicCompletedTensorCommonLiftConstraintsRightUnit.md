## What changed

Added a proved obstruction to the assigned statement, rather than another split of its hole:

- `Sheaf.CategoryTheory.TensorUnitComparisonUnique` proves
  `CategoryTheory.tensorUnitComparison_unique` by cancelling an isomorphism and transporting
  faithfulness from the identity functor through the left unitor.
- The item imports that module privately and proves
  `WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_right_unit_not_universal`.
  A nonidentity automorphism of the native unit obstructs the assertion that *every* independent
  tensor/unit datum satisfies the right-unit equation.
- Marked the original theorem `STATEMENT-DISPUTED` and recorded the exact obstruction in its
  DAG proof plan. Its statement and proof hole are retained for coordinated normalization repair.

This is a partial delivery of a proved statement obstruction, not a proof or weakening of the
original theorem. It changes no existing signature, definition, instance, attribute or public import.
There are no consumer adaptations or definition-change records.

Validation: `lcompile.py --all` compiled both delivered Lean modules without warnings
(1.3 seconds for the generic lemma; 7.5 seconds for the item). Node references and the
verbatim Lean declaration headers were checked locally. The delivery tool runs the
independent packet, importer and axiom checks.

## Proved and sorry left

Proved with no `sorry` in the new proof bodies:

- `CategoryTheory.tensorUnitComparison_unique`
  (`lem-sf-tensor-unit-comparison-unique`).
- `WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_right_unit_not_universal`
  (`lem-sf-adic-completed-tensor-right-unit-not-universal`).

The single original hole remains:

- `WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_right_unit`
  (`new-sf-adic-completed-tensor-common-lift-constraints-right-unit`), marked disputed.

Holes closed: 0 of 1. Holes added: 0. No obligation was restated under another name and no
new theorem was left with `sorry`.

## No longer needed

None. No original import or dependency is pruned. The finite-model plan cannot be used on an
arbitrary `data`: normalization must be repaired before deciding its actual proof dependencies.
The proved generic uniqueness module is used by the new obstruction proof.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: `CompletedTensorCommonLiftTensorUnit` contains just a natural tensor
isomorphism and a unit isomorphism. It does not say either is the finite comparison constructed
from `N`. The arguments `N` and `coherence` do not mention `data` at all. Consequently the
assigned theorem is universal over independently replaceable unit isomorphisms.

The formal obstruction fixes `data.tensor` and replaces `data.unit` by
`e ≪≫ data.unit`, for a nonidentity automorphism `e` of the native unit. Evaluate the proposed
law at the common coefficient unit for both records. Cancel the common tensorator and mapped
right unitor. Tensoring on the left by the ordinary common unit is faithful, since `data.unit`
identifies it with the native tensor unit. Thus the two unit maps agree; cancelling
`data.unit.hom` says `e.hom = 𝟙`, a contradiction. Every part of this argument is Lean code,
without invoking the disputed completed-lift theorem or its holed siblings. The proof uses
the existing common right-unitor isomorphism only as an isomorphism, not its normalization
equations; its construction still belongs to the existing source dependencies.

The obstruction makes its nonidentity automorphism an explicit hypothesis, so it does not claim
that the empty scheme has such an automorphism. For the intended nonzero characteristic-zero
coefficient category, negation of the unit is the usual example. The delivery does not claim
a separately formalized geometric instance or a proof of nontriviality of its native unit.

The same normalization issue affects the existing universal left-unit theorem and the theorem
assembling all four constraints. The sibling symmetry assertion likewise quantifies over an
arbitrary tensorator. Those statements need a coordinated repair of the selected comparison
interface; the finite-model proof cannot establish them merely from the *existence* of an
unrelated tensorator and unit. No sibling theorem is used to conceal this problem.

The initially explored route via left-unit and symmetry would additionally need the prescribed
common-stage braiding/unitor identity. No unconditional lemma asserting that identity is added:
the selected system calculus does not publicly retain the native tensor-coherence witness that
would justify its identification with the monoidal unitors. This is not needed by the delivered
obstruction proof.

## New nodes

`lem-sf-tensor-unit-comparison-unique` records the proved categorical cancellation lemma.
Its only ingredients are Mathlib's left-unitor natural isomorphism, transport of faithfulness
along a natural isomorphism, and cancellation of an invertible morphism.

`lem-sf-adic-completed-tensor-right-unit-not-universal` records the proved obstruction for the
actual `CompletedTensorCommonLiftTensorUnit` interface. Its mathematical assumptions and its
Lean declaration retain the nonidentity automorphism explicitly. There are no new holes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.TensorUnitComparisonUnique": "791007a8b5ab10b7e171050e02ac23bdd67b984f", "Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit": "b71e8f7354bbfa32784869b0de439307ca1abf05"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": {"hash": "0eca76ecbd74c77926bc1ebafe60cb4ed3e413b3", "status": "OK"}}, "seconds": 93, "time": "2026-10-28T10:26:40+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
