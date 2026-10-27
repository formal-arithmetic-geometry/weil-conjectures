## What changed

Proved the original `WeilConjectures.PurityFiniteSetting.finiteReduction_baseChangeSource`
from the strictly smaller ordinary shifted pullback cube, with explicit Lean proofs
of root-chart naturality and cancellation. The proof chooses compatible primitive
roots, applies both existing normalization theorems, moves the input comparison
through the smaller-level chart, and cancels that chart. Private helpers prove the
naturality of the tensor-unit shift, fixed root chart, intrinsic source chart and
actual scalar/pullback comparison. The generic tensor-shift naturality calculation follows the existing proved
private helper, reproduced locally to avoid importing unrelated purity obligations.

Added `Sheaf.Paper.FiniteReductionShiftedPullbackCube` and its node. It concerns
ordinary pullbacks and arbitrary integer shifts only: there is no Tate line, root,
purity map, exceptional inverse image, constructibility or Tor assumption. Updated
the item's proof plan, proof dependencies and origin to agree with the Lean proof.
Existing public signatures, definitions and public imports are preserved. No
source-library module is changed and no change record is needed.

Validation: the new cube module compiled through `lcompile.py --all`; the final
assigned module compiled without errors or warnings through `lcompile.py`
(41.5 seconds reported). Delivery preflight is run by `deliver3.py`.

## Proved and sorry left

Initial item holes: 1. Closed:
`WeilConjectures.PurityFiniteSetting.finiteReduction_baseChangeSource`
(node `lem-pur-finite-reduction-base-change-source`).

Added one hole:
`WeilConjectures.PurityFiniteSetting.finiteReduction_shiftedPullbackCube`
(node `lem-pur-finite-reduction-shifted-pullback-cube`).

This is a decomposition, not a net hole reduction: one hole closed and one
strictly simpler hole added. The item itself contains zero holes. All private
helpers are fully proved. The remaining theorem is exactly `:= by sorry` in its
own module, with its source and complete proof in words.

## No longer needed

No original public imports are removed and no modules or declarations are
withdrawn. The item no longer directly uses the large conjunction
`lem-fix-operation-reduction` / `Sheaf.Paper.BasicOperationsCoefficientReduction`:
its Lean statement does not supply the required shifted realization cube.
Replaced that proof dependency by the explicit smaller cube. The new cube's plan
uses the existing unshifted constant-ring cube
`lem-sp-constant-scalar-pullback-cube` and geometric localization theorem
`lem-weil-pbc-ringed-square-localization`, then the prescribed realization and
adjoint shift comparisons. This does not claim these nodes are unused elsewhere.

The root-chart naturality calculation follows the proved tensor-shift helper
from `Sheaf.SecSmoothPurity.SmoothPurityNaturality`, with its proof kept locally;
that module is not imported. It does not apply its purity naturality theorem or
assume a finite-Tor input. No exceptional or purity
coherence theorem is imported specially for this proof.

## Where the brief, the DAG or earlier work was wrong

The shared read-only mirror initially lacked the assigned module while retaining
its queue entry, node and F3 report. There was no rework row or quarantine file.
Recovered the exact original Lean source by reading the project server's live
repository into the sandbox. Its original statement and public imports are kept;
absence from the mirror was not treated as withdrawal authorization.

The node's proof compressed the shifted coefficient cube and root-chart
naturality into a prose step. The existing generic unshifted scalar cube is in
ring-sheaf tensor coordinates, whereas this item's square uses exact fixed-scalar
realization compositors. No existing statement directly gives both that transport
and the specified scalar-adjoint shift square. The new node states only this
ordinary coefficient step; the root/twist part is now implemented and proved.

Checked edge cases: arbitrary K (including zero or unbounded), arbitrary v,
dimension zero (unit charts), equal coefficient levels, empty schemes, and
nonflat quotient maps. The argument uses genuine derived extension of scalars,
never quotient flatness. The unit route is unchanged. Whole-blueprint reference search and whole-DAG searches found
no existing statement of this exact shifted intrinsic cube; the nearby module-
object and field-extension results use different coefficient functors/domains.

## New nodes

`lem-pur-finite-reduction-shifted-pullback-cube`, realized by
`Sheaf.Paper.FiniteReductionShiftedPullbackCube` and
`WeilConjectures.PurityFiniteSetting.finiteReduction_shiftedPullbackCube`, states
the coefficient/pullback cube with arbitrary integer shift and no Tate twist.
Its source is Steps 2 and 4 of the latest finite-reduction-of-purity proof.
The unshifted ring-sheaf cube is already proved in the library; the remaining
coordinate transport and adjoint shift compatibility are described separately
in its proof plan. Three kinds of Mathlib search, plus Loogle, whole-blueprint reference search
and a whole-DAG statement search, were performed. The combined new dependency graph was checked
for a path back to the item and has none. No change record is added.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
