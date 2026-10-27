## What changed

Repaired `realizationScalar_directImage_mate` in
`lean/Sheaf/Paper/FiniteRealizationScalarMate.lean`.  The global build had
begun unfolding `realizationScalarIso` through a proof-dependent right
isomorphism, so the former `simpa` proof of the local unit equation no longer
matched `realizationScalar_unit`.  The proof now uses `convert` followed by a
broad simplification, which resolves the proof-dependent casts while preserving
the same algebraic argument and statement.

## Proved and sorry left

Repaired the existing complete proof of
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationScalar_directImage_mate`.
The item has zero original holes; zero holes closed, zero holes added, and zero
holes remain.  This is a repair of a zero-sorry global-build failure.

Validation: compiled the unchanged mate-algebra and restriction-cube dependency
sources before this item, in import order.  The repaired item compiled without
errors or warnings in 8.1 seconds.  Temporary unchanged dependency copies were
removed from the delivery sandbox afterward.

## No longer needed

None.  The existing imports and proof-dependency nodes remain used.

## Where the brief, the DAG or earlier work was wrong

The previous proof compiled against the published dependency artifacts but
failed in the running global build after the dependency proof terms were
re-elaborated.  The statement and DAG route remain correct; the failure was a
proof-term elaboration mismatch involving the independently constructed
right-isomorphism proof inside `realizationScalarIso`.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
