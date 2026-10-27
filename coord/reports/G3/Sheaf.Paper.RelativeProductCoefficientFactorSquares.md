## What changed

Filled `WeilConjectures.relative_product_coefficient_factor_squares` with a real
conjunction proof.  The factor naturality clause is obtained from the naturality of
`R.factors`, and the two nonempty proper-coordinate clauses use the existing
`relative_product_proper_coordinates_exists` theorem.  The two structural parts
that remain substantial are now explicit, strictly smaller split-off theorems in
`RelativeProductFactorSquaresCore` and `RelativeProductProperCompatibilityCore`;
the item imports those proof-only modules.

## Proved and sorry left

Closed the hole in `WeilConjectures.relative_product_coefficient_factor_squares`.
The existing hole in `WeilConjectures.relative_product_presentation_exists` remains.
The delivery adds the named split-off holes
`WeilConjectures.relative_product_factor_squares_core` (node
`new-sf-relative-product-factor-squares-core`) and
`WeilConjectures.relative_product_proper_compatibility_core` (node
`new-sf-relative-product-proper-compatibility-core`).
`relative_product_proper_coordinates_exists` was already proved and remains proved.

## No longer needed

No imports or existing DAG nodes are pruned.  The main theorem no longer needs a
separate proof of factor naturality or a separate construction of proper coordinates:
these are supplied directly by `R.factors` naturality and
`relative_product_proper_coordinates_exists`.

## Where the brief, the DAG or earlier work was wrong

No statement was changed and no mathematical error was found.  The original proof
plan bundled the primitive coefficient-square calculation and the proper conjugation
calculation into the item theorem; both are genuine strict subclaims and are recorded
as separate nodes so they can be proved independently.

## New nodes

`new-sf-relative-product-factor-squares-core` records the six primitive coefficient
factor squares.  `new-sf-relative-product-proper-compatibility-core` records proper
normalization, proper coefficient comparison, and the conjugated proper factor
squares.  Their Lean modules and node files are included in this delivery.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
