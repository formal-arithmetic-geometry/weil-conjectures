## What changed

Proved `WeilConjectures.OpenSemilinearTensor.openScalarTransitionCompatibility` from
the supplied quotient-compatible ordinary reductions, finite tensor comparison,
and normalized open-system adjunction. Both composites agree on original scalar
unit generators; the scalar and localized-open adjunction Hom equivalences extend
that agreement to the whole sheaf. The original public signatures and the complete
`scalarLevelComparison` definition are unchanged.

Added the fully proved support module `Sheaf.SixFunctors.OpenSystemUnitSections`
for section transport, horizontal unit naturality and finite summand normalization.
The first complete single-file proof compiled in 59.6 seconds. After improving the
local transparency of carrier constructions, the support module separates the
self-contained open-system calculation to leave room under the per-file limit.
All imports added to the item are proof-only. The existing generic quotient-unit
helpers are reused with arbitrary `n ≤ m`; their public successor theorem is not
assumed to apply to arbitrary ordinary reduction data.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenSemilinearTensor.openScalarTransitionCompatibility`.
Also proved `WeilConjectures.OpenSemilinearTensor.systemUnit_evaluation` in the new
support module. Added zero holes and zero split-off unproved statements. There is
no `sorry` in either delivered module. The final two-file layout passed
`lcompile.py --all` (exit 0).

## No longer needed

None. The original public import is needed for the statement and definitions.
The proof implements all three original proof steps. It uses the existing proved
generic quotient-unit helpers, rather than the generic existence theorem for
semilinear slice scalar comparisons; that existence theorem was not a dependency
of this item and is not proposed for withdrawal.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing plan works directly and does
not require another unproved reduction. The difficult implementation details were
carrier conversions through pushforward and restriction of scalars; local
transparency settings and abstract equality lemmas keep those checks bounded.
The unit route is retained, including arbitrary quotient maps and the empty open.

## New nodes

`lem-sf-open-system-unit-sections` records the fully proved finite normalization of
the actual system adjunction unit in `Sheaf.SixFunctors.OpenSystemUnitSections`.
Its section maps are explicit constructions, and the theorem follows from
`unit_evaluation`, identity restriction evaluation, `transportSections`, naturality
and the prescribed localized summand unit. This is a proved step, not a new hole.
No existing shared interface changed, so no change record or forced adaptation is
needed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
