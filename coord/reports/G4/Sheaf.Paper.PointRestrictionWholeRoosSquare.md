## What changed

Proved the whole point-restriction Roos square using the existing simultaneous comparison data.
The sections comparison is its canonical cone comparison; the inverse-image comparison is composed
with the inverse coefficient identification. Both coordinate formulas follow from the diagonal
and product-projection equations. A sectionwise calculation identifies the specified system
transport with ambient restriction, and product/biproduct extensionality proves the strict square.
The derived-limit normalization is obtained from the existing normalizedRoosIso proof API, and
its naturality gives the final transport equation. Existing signatures and definitions are retained.

The node's proof, proof dependencies and proof origin follow this route. All added helpers are
private, proved calculations inside the item module. The constructed inverse-image comparison
is a private definition with a proved coordinate API; keeping its composite associators behind
that API avoids repeated kernel expansion and brings compilation below 60 seconds.
No source-library file is changed.

## Proved and sorry left

Closed: WeilConjectures.PointRestrictionWholeRoos.point_restriction_whole_roos_square.
Original holes: 1. Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in this delivery.
The proof uses the previously stated point_system_normalized_comparison_data and exact_products;
those pre-existing dependencies retain their own proof obligations.

The complete module compiled in 50.1 seconds after explicitly selecting the comparison API
instances in the strict-square calculation. Its one line-length warning was fixed by wrapping
the line. The earlier delivery attempt pushed nothing because its compile took 71 seconds;
the revised packet includes the sections comparison API and explicit square instances.
The revised delivery compile and axiom probe passed in 54.6 seconds; its remaining
line-length warning was then fixed.

## No longer needed

The proof does not invoke lem-cbc-exact-product-functor-strict-limit directly: the existing
simultaneous comparison-data declaration already supplies its canonical products and cone maps.
It does not separately invoke lem-weil-pbc-localization-universal-property or reconstruct the
inverse-image equivalence and exact sections. PointAutomorphismRestrictionNatural and
PointSystemTransportDescent already give the requested descent and representative equations.
The scalar normalization uses the proved normalizedRoosIso API and strictTowerLimitIso, rather
than invoking the general ringed strict Roos comparison again.

No module is withdrawn: these dependencies remain used by existing declarations and by the
simultaneous comparison data. No target or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's planned direct construction of both product comparisons duplicates the existing
PointSystemNormalizedComparisonData interface. Its normalized comparison data is a shorter
available route; the remaining strict square requires an actual sectionwise calculation and
both cone coordinates, which are proved here. No mathematical statement was found false.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
