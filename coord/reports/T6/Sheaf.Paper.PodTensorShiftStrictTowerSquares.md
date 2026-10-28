## What changed

Filled `WeilConjectures.podTensorShift_strictTowerSquares` without changing its
statement or its public import. Its proof pairs two fully proved calculations,
`podTensorShift_strictTowerLeftSquare` and
`podTensorShift_strictTowerRightSquare`, in the corresponding new modules under
`Sheaf.Paper`. Each square is precomposed with the inverse tensor comparison.
Existing proved finite tensor extensionality then reduces it to unit reduction
generators. Quotient, inverse tensor, forward tensor and signed shift laws
compute both paths. Integer degree transport handles total degrees; additivity
handles the right-slot sign.

The new files use proof imports of the private proved finite tensor APIs in
`IntegralScalarTensorLevelReduction` and `IntegralScalarTensorLevelTower`.
Three proved private helpers in each generator file package unit quotient normalization,
dependent evaluation at equal degrees, and the finite tensor map calculation. The square modules contain only the
structural extensionality argument and call their generator calculations.
Local reducibility settings expose the section carriers under reindexing and
restriction of scalars. Profiling found expensive checking of the expanded tower
types; the two calculations were placed in separate files after those local
unfolding improvements, following the brief's compile-time instructions.
No existing definition, instance, attribute or signature is changed globally.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.podTensorShift_strictTowerSquares`
(node `lem-pod-tensor-shift-strict-tower-squares-c3`).
Both new lemmas are fully proved:
`WeilConjectures.podTensorShift_strictTowerLeftSquare` and
`WeilConjectures.podTensorShift_strictTowerRightSquare`.
The new generator lemmas
`WeilConjectures.podTensorShift_strictTowerLeftGenerator` and
`WeilConjectures.podTensorShift_strictTowerRightGenerator` are also fully proved.
There are zero holes in all five delivered modules. No new `sorry` was added.
The delivery closes the original obligation without adding an unproved reduction.

All five files compiled without warnings in import order: left generator 47.5 s,
right generator 47.3 s, left square 30.3 s, right square 30.5 s, item 31.5 s.
An explicit `#print axioms` audit found the standard axioms plus inherited
`sorryAx`. The existing `PodCompletionReindex` and `PodCompletedTensorReindex`
structure declarations themselves already have that dependency; the signed shift,
tensor tower and ordinary reindexing complex declarations have only standard
axioms. No new `sorry` or axiom occurs in this packet. The scratch audit module
was removed before delivery.

## No longer needed

No modules or nodes are withdrawn. No original import is removed.
The proof avoids a separate lemma identifying shifted quotient maps on arbitrary
sections: precomposition by `T.tower.inv` permits testing unit reduction generators,
where `D.QuotientGenerators` already suffices. The original finite-tensor
construction dependencies remain through the two proved square calculations.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned generator calculation works, including
zero and negative shifts. The proof route now records the inverse tensor generator
law and the existing unit-generator extensionality and finite tensor map lemmas
explicitly. No unit-level proof step is bypassed.

## New nodes

`lem-pod-tensor-shift-strict-tower-left-square-t6` records the fully proved
left-slot equality in `Sheaf.Paper.PodTensorShiftStrictTowerLeftSquare`. It is one
of the two equalities in the original conclusion, proved from the existing
normalization laws and finite tensor generator API.

`lem-pod-tensor-shift-strict-tower-right-square-t6` records the fully proved
right-slot equality in `Sheaf.Paper.PodTensorShiftStrictTowerRightSquare`. Its
calculation also uses additivity to transport the Koszul sign. These two nodes
separate checked proofs into files; neither is an unproved obligation.

`lem-pod-tensor-shift-strict-tower-left-generator-t6` records the fully proved
pointwise unit-generator calculation in
`Sheaf.Paper.PodTensorShiftStrictTowerLeftGenerator`. It is strictly part of the
left-square proof, before complex and natural-transformation extensionality.

`lem-pod-tensor-shift-strict-tower-right-generator-t6` records the analogous fully
proved calculation, including the sign, in
`Sheaf.Paper.PodTensorShiftStrictTowerRightGenerator`. The generator calculations
and structural extensionality were separated after profiling the kernel checks.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodTensorShiftStrictTowerLeftGenerator": "92c812a1a25eb0657bb0647fc3a54009422e00a2", "Sheaf.Paper.PodTensorShiftStrictTowerLeftSquare": "9b6b16e2cb478cb64ebdfb55a1a08c66a0772a9f", "Sheaf.Paper.PodTensorShiftStrictTowerRightGenerator": "ef9616bea112550ba70a26060aa4e37f0af15ead", "Sheaf.Paper.PodTensorShiftStrictTowerRightSquare": "6001dc8c9bddecb1b8e72f4a2263e15adc666d07", "Sheaf.Paper.PodTensorShiftStrictTowerSquares": "63d52f764f096c55aeb659d6425c01b1d5d617ea"}, "results": {}, "time": "2026-10-28T11:11:51+0800", "transitive": 0, "version": 1}
```

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
