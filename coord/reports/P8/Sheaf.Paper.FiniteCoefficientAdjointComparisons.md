## What changed

Partial arithmetic delivery in `Sheaf.Paper.FiniteCoefficientAdjointComparisons`.
Added proved public theorems `stage_ramification` and `stage_finiteFree`.
The former expands the actual image of the base uniformizer in the upper DVR,
identifies its power ideals and proves cofinality. The latter proves that every
same-level arrow is finite free using integral closure, finite torsion-free
freeness over a DVR, and quotient base change. Both are parts of the original
node's arithmetic argument and retain ramified extensions.

Existing public statements and definitions are unchanged. Four private arithmetic
imports support the new proofs. Local instance priorities avoid unrelated
instance searches; no global instance attribute is changed.

## Proved and sorry left

Proved `AlgebraicGeometry.FiniteCoefficientAdjoints.stage_ramification` and
`AlgebraicGeometry.FiniteCoefficientAdjoints.stage_finiteFree` with no new holes.
Original holes closed: 0 of 1. Holes added: 0.
The original hole remains in
`AlgebraicGeometry.FiniteCoefficientAdjoints.finite_coefficient_adjoint_comparisons`
(node `lem-pur-finite-coefficient-adjoint-comparisons`). This is partial arithmetic
work, not completion or decomposition of that theorem. No data is chosen from
an unproved existence statement.

The separate geometric candidate was not submitted: although its transport and
mate calculations were developed, the combined module repeatedly exceeded the
60-second compilation limit. No claim of a checked full geometric proof is made.

## No longer needed

None. The original proof-dependency imports and DAG route are retained. The
unsubmitted geometric experiments are outside the delivery's Lean tree.

## Where the brief, the DAG or earlier work was wrong

The arithmetic must use the image of the base uniformizer, which can have positive
ramification exponent in the upper field. Replacing that image by the upper
uniformizer at the same index would change the coefficient ring. The delivered
proofs keep the actual parameter and derive the cofinal index e*n.

## New nodes

`lem-pur-stage-ramification-cofinality` records the proved DVR expansion,
power-ideal equality and cofinality of the actual stage parameter.
`lem-pur-stage-same-level-finite-free` records finite freeness of the actual
same-index quotient map. Both attach to the corresponding public theorems in
the item module; neither introduces a new module or a sorry.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
