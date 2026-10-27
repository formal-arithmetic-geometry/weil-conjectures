## What changed

Proved `AlgebraicGeometry.Etale.rawRestricted_resolution_shift_square` in
`Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle` without changing its statement
or any existing definition. Private categorical helpers express compatibility of the
right-derived unit, the resolution comparison, the augmentation and homology with shifts.
The proof follows the existing node plan, now recorded with its generic categorical
calculation in the node copy. A private proof import supplies shift
compatibility for natural transformations of complexes.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.rawRestricted_resolution_shift_square`
(node `lem-weil-pbc-raw-restricted-resolution-cocycle`).
One original hole closed; zero holes added or split off. No sorry remains in the item.
All added private helpers are proved. The complete module compiled without warnings
in 46 seconds through lcompile.py.

## No longer needed

None. The original public import and all definitions remain necessary. The resolution
evaluation module supplies `resolutionSectionsIso`; its separate evaluation theorem is
not needed for this equality of morphisms. Etale preservation of injectives and
K-injectivity under shift remain used by the existing shifted-resolution lemma.
No unit route, module or DAG dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The canonical shift structures and augmentations give the stated square,
including degree zero and an empty chart. The proof uses no positivity restriction
on the integer shift in its general categorical helpers.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
