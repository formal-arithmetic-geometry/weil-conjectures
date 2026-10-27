## What changed

Copied `Sheaf.Paper.ProEtaleProjectionMateExact` into the S4 sandbox and proved its target by unpacking two strictly simpler interfaces. Added `proEtaleProjectionMateShiftData` for the two shift structures and triangulatedness, and `proEtaleProjectionMateData` for the specified mate, shift compatibility, and coefficient-unit isomorphism. The latter is stated under the shift-structure instances supplied by the former.

## Proved and sorry left

The original `proEtaleProjectionMateExact` sorry is closed by a direct existential construction. Two strictly simpler declarations remain sorry for parallel proof work:

- `AlgebraicGeometry.Scheme.proEtaleProjectionMateShiftData`.
- `AlgebraicGeometry.Scheme.proEtaleProjectionMateData`.

Thus one original hole is closed and two decomposition holes are added.

## No longer needed

Change record: `coord/changes/proetale-projection-mate-exact-s4.md`.

No Lean imports were removed. The direct proof no longer uses these original planned proof dependencies: `lem-weil-pbc-localization-universal-property`, `lem-weil-pbc-ringed-projection-mate-exact`, and `lem-weil-pbc-resolving-representative-whiskering`. The inverse-image, native-operation, and generic tensor-pullback declarations remain transitive statement dependencies of the split interfaces.

## Where the brief, the DAG or earlier work was wrong

The generic ringed projection-mate theorem cannot be applied directly because its corner fixes the site-object, site-morphism, and coefficient universes together, while the native pro-etale operations use distinct universes. The split interfaces record the required native-universe transport instead of asserting that generic application.

## New nodes

- `lem-weil-pbc-proetale-projection-mate-shift-data-s4` — `Sheaf.Paper.ProEtaleProjectionMateShiftData`.
- `lem-weil-pbc-proetale-projection-mate-data-s4` — `Sheaf.Paper.ProEtaleProjectionMateData`.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
