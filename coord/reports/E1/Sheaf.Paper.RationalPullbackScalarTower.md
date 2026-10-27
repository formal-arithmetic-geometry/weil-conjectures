## What changed

Filled `WeilConjectures.rationalPullbackScalarComparison_tower` in
`Sheaf.Paper.RationalPullbackScalarTower`, preserving its statement and public imports.
Private proved helpers identify the normalized ordinary/completed comparison, transport
the existing ordinary pullback tower equation through completion, restrict it to the
intrinsic constructible categories, and transport the resulting equality through raw
rational localization using the prescribed component and pure-tensor formulas.
The item's DAG proof now describes these calculations explicitly.

Validation: `lcompile.py` accepted the final module without warnings in 9.2 seconds.
The public theorem signature and both original public imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.rationalPullbackScalarComparison_tower`
(node `lem-weil-rational-pullback-scalar-tower`). Added zero holes and split off zero
statements. No `sorry` remains in this module. The proof uses the existing
`scalarOperationsOrdinary_tower` declaration as required by the staged dependency route;
this delivery does not claim to discharge its independent proof obligations.

## No longer needed

None. Both original public imports are required by the theorem's statement. All three
existing proof dependencies are used, and the unit route is preserved. No module or
node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing component normalizations suffice for
the proof; no new statement, definition repair, or downstream adaptation is needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
