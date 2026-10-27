## What changed

Proved `WeilConjectures.fdCommonStageConeIdentification` in
`Sheaf.Paper.FdShiftTriangleReflection`, following step 3 of the existing node
`lem-fd-shift-triangle-reflection`. The triangle isomorphism uses `isoToStage`
at the two endpoints and the identity on the cone object. Its three squares
are checked explicitly. The endpoint representatives follow from the existing
normalized right-unit associator. The connecting-arrow formula follows from
shift compatibility of `transIso`, cancellation of the scalar-shift comparison,
and naturality of the unit. Six private helpers isolate these calculations.

The proof privately accesses the existing right-unit normalization theorem in
`Sheaf.Paper.FiniteStagePairCategory`. Local irreducibility attributes protect
scalar extension, its associator, the concrete shift constructions, and the
underlying derived-category and localization instances against expensive unfolding. All existing public declarations, signatures, definitions
and public imports remain as before.

## Proved and sorry left

Closed one of the module's two holes:
`WeilConjectures.fdCommonStageConeIdentification`.

One original hole remains: `WeilConjectures.fdShiftTriangleReflection`
(node `lem-fd-shift-triangle-reflection`). Its original statement and complete
proof docstring remain intact. No holes are added and none are split off.
All private helpers are proved. The complete module compiled in 48.3 seconds
with profiling diagnostics; those diagnostics are removed for delivery. This is a partial delivery: the main theorem
retains its original hole while its explicit common-stage cone companion is closed.

## No longer needed

No nodes or modules are withdrawn. No imports are removed. The cone calculation
needs no distinguishedness hypothesis: the specified isomorphism is valid for
any finite triangle, including zero arrows, but the existing hypothesis and
signature are preserved. The rest of the module still requires the original
planned dependencies for shift descent and finite-model reflection.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is required. The normalized repeated-stage transports
must be retained: the endpoint representatives use the inverse unit and the
connecting arrow uses the unit before the finite connecting map and inverse
scalar-shift comparison. The original cone theorem's `hdist` hypothesis is
stronger than the calculation needs; it has not been removed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
