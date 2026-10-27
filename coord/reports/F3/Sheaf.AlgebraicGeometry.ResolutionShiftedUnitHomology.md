## What changed

Proved `AlgebraicGeometry.Etale.resolution_shifted_unit_homology` without changing its statement. The proof uses the existing canonical resolution homology comparison for the unshifted case, then transports the derived unit and prescribed augmentation through shifts. All new quotient, unit, and homology compatibility helpers are private and proved. Private generic versions of the shifted resolution and augmentation use the same constructions as the original definitions. The calculation keeps the additive functor abstract until the final specialization, avoiding expensive kernel conversion of concrete sheaf pushforward data. Updated the node proof to describe this argument.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.resolution_shifted_unit_homology`.
Added zero holes; no `sorry` remains in the delivered module. No statements were split off.

Validation: the full proof compiled through `lcompile.py` in 43.8 seconds with profiling enabled. Profiling options were removed before delivery; `deliver3.py` runs the final compilation and delivery checks.

## No longer needed

None. Both planned proof dependencies remain needed. The proof adds only the private proof import `WeilConjectures.CategoryTheory.CanonicalResolutionHomologyComparison`; the original public import remains necessary for the statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The planned unshifted comparison suffices, but the shifted calculation requires explicit compatibility instances and associators for the bounded-below quotient and termwise functors. These are constructed and proved locally; no existing interfaces or definitions were changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
