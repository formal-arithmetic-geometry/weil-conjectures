## What changed

Repaired the local scalar-unit calculation in
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`
(`lean/Sheaf/Paper/FiniteRealizationScalarMate.lean`). The unit lemma now applies
by a bounded `simpa only`, explicitly normalizing the equality transport inside
`realizationScalarIso` with `eq_mpr_eq_cast`, `cast_eq`, and `id_eq`.
This replaces the recent `convert` and unrestricted simplification workaround.
The theorem signature, definitions, visibility, imports, and mathematical proof
route are unchanged. No other existing module is delivered.

## Proved and sorry left

This is the assigned zero-hole global-build repair, not a new hole closure.
The repaired declaration is
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`
(node `lem-finite-realization-scalar-mate`). Original holes: 0; closed: 0;
added: 0; remaining: 0. No split statements or new axioms were introduced.

Validation: the current unchanged `FiniteRealizationRestrictionCube` source
compiled in 47.3 seconds before the item was repaired. The final repaired item
compiled without errors or warnings in 9.9 seconds. Its unchanged direct
consumer `FiniteProperScalarTransport` compiled in 31.6 seconds with the sandbox
artifact overlay. An additional full-chain check stopped at the unchanged cube
because that run took 71 seconds, exceeding the 60-second per-file limit; it did
not reach the item or consumer. No limit was raised. Both unchanged test copies
were removed from the delivery sandbox. The cube timing failure is outside the
single delivered proof edit and is recorded here rather than represented as a
passing full-chain check.

## No longer needed

None. All imports and all existing proof dependencies remain used. The unit,
restriction-cube, and inverse-mate argument is retained; no node or module is
withdrawn or bypassed.

## Where the brief, the DAG or earlier work was wrong

The current rework record reports a mismatch between the generic scalar-unit
lemma and the concrete left-adjoint uniqueness comparison. Reproducing the old
`simpa` failure showed that the concrete comparison contains an equality cast
around its inverse realization/restriction square. Merely unfolding the named
comparisons does not normalize that transport. The current source already
contains C2's recently landed broad `convert` workaround; this delivery retains
its intended repair while making the cast normalization explicit and allowing
a direct application of the unit lemma. The statement and DAG route are correct.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
