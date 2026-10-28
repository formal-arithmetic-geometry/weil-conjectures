## What changed

Added `Sheaf.Paper.AdicCompletedTensorCommonLiftUnitNormalization` and proved
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_unit_normalization`.
For any fixed tensorator, it constructs the unique unit comparison satisfying the
right-unit equation at the common coefficient unit U. The construction lifts the
isomorphism rho_(ordinary U) followed by the inverse tensorator/unitor composite
along the fully faithful functor ordinary(U) tensor -.

The item's existing theorem
`completed_tensor_common_lift_right_unit_not_universal` now uses this constructive
normalization theorem. Its statement is unchanged. The item's public imports and
all existing declaration signatures are unchanged. Both files are compiled alone
in dependency order through lcompile.py; delivery repeats the required probes.

This is a partial delivery supplying a proved normalization step, not a proof or
statement repair of the disputed universal claim. No other existing Lean module
is changed. Change record:
`coord/changes/F3-adic-common-lift-unit-normalization.md`.

## Proved and sorry left

Closed 0 existing holes; added 0 holes. The item's original hole remains:
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_right_unit`
(node `new-sf-adic-completed-tensor-common-lift-constraints-right-unit`).
Its existing STATEMENT-DISPUTED marker and signature are preserved.

The new theorem
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_unit_normalization`
(node `lem-sf-adic-completed-tensor-common-lift-unit-normalization`) is fully proved,
with no direct sorry. The existing
`completed_tensor_common_lift_right_unit_not_universal` remains fully proved.
The new theorem is a positive existence-and-uniqueness result; it neither restates
nor moves the original hole. No split-off sorry theorem is added.

## No longer needed

Removed the item's direct proof import
`Sheaf.CategoryTheory.TensorUnitComparisonUnique`, replacing it with the new
normalization module. The generic uniqueness theorem remains used by that new
module, so its node and module are still needed transitively. No module or node
is pruned. The finite-model and native-coherence dependencies of the outstanding
claim are retained; no replacement argument for that claim is asserted.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned remaining theorem quantifies over every arbitrary
`CompletedTensorCommonLiftTensorUnit` datum. Its two fields are unrelated
isomorphisms, with no equations relating either field to N or coherence. A
nonidentity automorphism e of the native unit changes data.unit to e followed by
data.unit without changing any hypothesis. The already proved obstruction shows
that the right-unit law cannot hold for both choices. The new theorem pinpoints
the issue: even at U there is exactly one valid unit comparison for a fixed
tensorator, whereas the assigned statement permits all of them.

The new theorem uses the given data.unit only to prove that ordinary(U) is
isomorphic to the native unit. Uniqueness makes the resulting normalized unit
independent of that initial isomorphism. It is valid for a zero category or an
empty scheme as well; no nontriviality or characteristic assumption is used.

A repair must construct jointly normalized tensor/unit data and prove the
constraint equations for that selected data. Supplying the original theorem with
its desired conclusion as a new premise, or moving the same universal assertion
to a fifth split, would not repair it. The parent constraint theorem currently
quantifies over the same arbitrary data and therefore shares the defect. This
packet does not silently weaken that parent or any target.

I also checked the potential shortcut from left-unit compatibility and symmetry.
It needs the source identity beta_(A,U) followed by lambda_A = rho_A. The source
operations are reconstructed separately, and their published interface does not
supply that identity for the selected coefficient calculus. In particular,
`pullbackTensorCalculus` retains systemClosed and systemTensorModel, but no
RingedDerivedTensorCoherence witness for that selected pair. A merely existential
symmetric calculus at another witness cannot normalize the selected maps.

## New nodes

`lem-sf-adic-completed-tensor-common-lift-unit-normalization` records the proved
unique normalization at U in its own module. Its existence proof uses Mathlib's
full-faithfulness transport and preimageIso; uniqueness uses the existing node
`lem-sf-tensor-unit-comparison-unique`. The statement is strictly local to U and
makes no assertion about arbitrary unit choices or constraint laws at all
objects. The existing obstruction node's proof and proof_deps now cite it.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit": "147b243d2c8bb2e7faa46a580233f397e728ba5b", "Sheaf.Paper.AdicCompletedTensorCommonLiftUnitNormalization": "23fec6f3e916119e4e66be3914a2e656b3c51801"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": {"hash": "0eca76ecbd74c77926bc1ebafe60cb4ed3e413b3", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T12:05:38+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
