## What changed

Replaced the hole in
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_right_unit`
by a categorical cancellation proof from the existing left-unit and associativity
component declarations and the triangle identity for the prescribed common-stage
tensor. The private helper `right_unit_of_left_associativity` proves the implication
with all of these equations as explicit hypotheses. Tensoring on the right by the
realized coefficient unit is faithful, since `data.unit` identifies that object
with the native tensor unit; naturality, associativity and the triangle cancel
the additional factor.

Added `Sheaf.Paper.CommonStageTensorTriangle`. Its source-documented proof obligation reflects the integral
triangle through faithful coherent reduction, localizes it to rational
coefficients, and compares common-stage representatives at one sufficiently
large finite field. The attempted full transport was preserved in scratchpad,
but not delivered; the final theorem has exactly the named `sorry` body. Every map is the prescribed comparison; no monoidal
structure is assumed on the common-stage category.

All existing public signatures are preserved. Only private proof imports were
added to the item. The obstruction proof now uses a record update when twisting
the unit, preserving every field supplied by future normalization repairs.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_constraints_right_unit`
(node `new-sf-adic-completed-tensor-common-lift-constraints-right-unit`).
The existing obstruction theorem
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_right_unit_not_universal`
remains proved. Split off the strictly smaller pending declaration
`WeilConjectures.commonStageTensor_triangle`
(node `lem-pur-common-stage-tensor-triangle`). One hole is added in `WeilConjectures.commonStageTensor_triangle`; none remain
in the assigned item. This is a decomposition: one upper hole closed and one
lower hole added, net zero.

This closes a local hole by reduction to existing named declarations. It does
not assert that its transitive axiom set is sorry-free: the imported left-unit
and associativity declarations and several existing coefficient construction
specifications remain pending. In particular, their normalization defects below
are not discharged by this categorical implication.

## No longer needed

No public imports or existing modules were removed. There is no new
right-unit-specific finite comparison statement. The direct finite-representative
right-unit calculation planned in the item's old node is redundant once
associativity, left unitality and the common-stage triangle are supplied.

Removed the item's direct proof dependencies on
`def-sf-adic-completed-tensor-finite-models`,
`def-sf-native-adic-realization-data` and
`def-zl-ringed-derived-closed-symmetric-monoidal-data`: these remain statement
and transitive dependencies, and are not globally pruned. The old obstruction
node `lem-sf-adic-completed-tensor-right-unit-not-universal` is no longer a proof
dependency of the positive theorem; its separate declaration remains in this
module and still uses the normalization theorem. No unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

The current server queue still marks the item disputed; there is no rework or
build-error record for it. The arbitrary `data.unit` defect recorded by D3 and
F3 is real. The new proof does not infer compatibility with arbitrary comparison
data directly from finite models: it uses the already stated left-unit and
associativity claims. These claims themselves have STATEMENT-DISPUTED comments
and pending proofs, and require a coordinated normalization repair. The
obstruction theorem and dispute comments are preserved. The new generic helper
makes the valid conditional implication explicit, without using an obstruction
to derive a contradiction.

The former DAG proof plan isolated a separate finite right-unit calculation.
Categorical cancellation makes this calculation unnecessary; the new proof
requires only associativity at (A,U,U), left unitality at U, and the common-stage
triangle at (A,U). The latter statement concerns prescribed maps only and does
not mention the arbitrary common-lift data, so it does not repeat the original
false universal claim under another name.

## New nodes

`lem-pur-common-stage-tensor-triangle` records the triangle identity for the
prescribed common-stage tensor, associator and unitors, together with its proof
by coherent reduction, rational localization and same-field representatives.
It is the one split-off hole. Empty schemes, zero inputs, identity stage extensions,
and repeated unit factors impose no extra hypotheses. The change record is
`coord/changes/G2-common-stage-tensor-triangle.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit": "04df3a02954ad43631b0c4c6da5cdd635030e29c", "Sheaf.Paper.CommonStageTensorTriangle": "4dddab233f51e005107e11410528fd45149c99f8"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonLiftConstraints": {"hash": "0eca76ecbd74c77926bc1ebafe60cb4ed3e413b3", "status": "OK"}}, "seconds": 247, "time": "2026-10-28T14:37:30+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
