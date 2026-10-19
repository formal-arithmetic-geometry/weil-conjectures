## What changed

Retained and checked the earlier proof work against the current module. The coefficient
comparison is the existing completed-coefficient comparison. Exactness of the two module
terms follows from ringed open-closed localization, transport of coefficient modules,
and uniqueness of adjoints. The three finite-type/Noetherian helpers use Mathlib.
The private triangle argument proves uniqueness and naturality from cross-object vanishing.
Additional private helpers show that the actual closed unit is epic, using uniqueness
of adjoints and the ringed localization sequence.

## Proved and sorry left

Five original holes closed: `WeilConjectures.sfRecollementCoefficientMap_isIso`,
`WeilConjectures.sfRecollementModule_exact`, `WeilConjectures.sfRecollementNoetherian`,
`WeilConjectures.sfRecollementOpenFiniteType`, and
`WeilConjectures.sfRecollementGeometricNoetherian`.

Five original holes remain, all belonging to
`prop-sf-open-closed-triangle-all-stages`:
`WeilConjectures.sfOpenClosedTriangle_finite`,
`WeilConjectures.sfOpenClosedTriangle_integral_rational`,
`WeilConjectures.sfOpenClosedTriangle_qbar`,
`WeilConjectures.sfOpenClosedTriangle_rational_weil`, and
`WeilConjectures.sfOpenClosedTriangle_qbar_weil`.
No holes added.

## No longer needed

None yet. Existing proof-dependency imports remain while the five stage statements
are being proved.

## Where the brief, the DAG or earlier work was wrong

Ordinary file compilation of the retained work succeeds against the current server.
The mandatory delivery dry run repeatedly fails before preflight with
`no answer from the compile server` (191, 192, and 190 seconds). No delivery was pushed.
The launcher scripts have not been modified or bypassed.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
