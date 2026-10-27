## What changed

Proved `AlgebraicGeometry.Etale.ClopenMateNormalization.lift_clopen` in
`Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization`. Openness follows from
`IsOpenImmersion.of_comp` and the first pullback projection. Properness follows
from `IsProper.of_comp` and the second pullback projection; the open preimmersion
with closed range is a closed immersion. Updated the first proof step of
`lem-cbc-etale-clopen-mate-normalization` to record this shorter geometry argument.
All declaration signatures, definitions, and imports are unchanged.

## Proved and sorry left

Closed one of the three original holes:
`AlgebraicGeometry.Etale.ClopenMateNormalization.lift_clopen`.
Added zero holes and split off zero statements.

Two holes remain, both attached to
`lem-cbc-etale-clopen-mate-normalization`:

- `AlgebraicGeometry.Etale.ClopenMateNormalization.etaleClopenMateNormalization`.
- `AlgebraicGeometry.Etale.ClopenMateNormalization.etaleClopenMateResolution`.

This is a partial delivery. The ordinary support-inclusion calculation and the
localized adjunction representative calculation are unfinished. Their original
named theorem bodies remain exactly `by sorry`; no partial proof contains a hole.
The geometry proof was checked in the earlier baseline compile. Recent retries
returned no answer from the compile service and did not check the later scratch
calculations; these calculations are excluded from this packet.

## No longer needed

No imports or modules are withdrawn. The separate cartesian-square construction
in the old geometry proof plan is unnecessary: cancellation of an open immersion
already proves the lift is open. The existing dependencies of the remaining
normalization argument are retained.

## Where the brief, the DAG or earlier work was wrong

The geometry plan was longer than needed. No statement error was found. Repeated
compile-service responses saying no answer prevented validation of the unfinished
representative and derived-normalization calculations; those responses are not
Lean errors and are not treated as evidence against the statements.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
