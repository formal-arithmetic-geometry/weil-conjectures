## What changed

The item module now proves both full finite-product identities from `Pi.hom_ext`,
using the corresponding coordinate projections.  I added the proof-only imports
`Sheaf.Paper.ProperBiproductCoordinate` and
`Sheaf.Paper.StrictProperBiproductCoordinate`.  Each coordinate theorem is a
strictly smaller named obligation and is recorded as a new DAG node.

## Proved and sorry left

The full declarations `proper_biproduct` and `strictProper_biproduct` are proved
by finite-product extensionality.  Two coordinate obligations remain as named
`sorry`s: `proper_biproduct_coordinate` in
`Sheaf.Paper.ProperBiproductCoordinate`, and
`strictProper_biproduct_coordinate` in
`Sheaf.Paper.StrictProperBiproductCoordinate`.

## No longer needed

No imports or declared dependencies were removed.  The proof uses the finite
coordinate data and product extensionality; no additional dependencies from the
original broad proof plan were introduced beyond the two split coordinate nodes.

## Where the brief, the DAG or earlier work was wrong

The original module left the two whole-map biproduct identities as opaque holes.
The implementation makes the intended finite-free column argument explicit as
coordinate statements and derives each recorded whole-map equality by
`Pi.hom_ext`.

## New nodes

`lem-pur-compact-support-strict-scalar-mate-proper-coordinate` records the
coordinate form of `proper_biproduct`.

`lem-pur-compact-support-strict-scalar-mate-strict-coordinate` records the
coordinate form of `strictProper_biproduct`.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
