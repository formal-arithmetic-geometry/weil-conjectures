## What changed

Proved `WeilConjectures.relative_product_proper_coordinates_exists` in
`Sheaf.Paper.RelativeProductCoefficientFactorSquares` without changing any existing
signature, definition or import. A proved private helper constructs the restricted
proper direct-image functor with `ObjectProperty.lift`, transports the specified
ambient proper identification across `supportNormalization`, and lifts that natural
isomorphism through the fully faithful inclusion. Its component equation follows
from `map_preimage` and `eqToHom_comp_heq`.

For finite and integral coefficients, preservation is exactly the corresponding
`SixFunctorDatum` coherence field `directDomain`; properness supplies separatedness.
For rational and common coefficients the domain is the whole constructible category.
This is a construction from the supplied functors, with no arbitrary witness chosen
from an unproved existence theorem.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.relative_product_proper_coordinates_exists`.

Two existing holes remain unchanged, both attached to
`lem-sf-relative-product-coefficient-factor-squares`:

- `WeilConjectures.relative_product_presentation_exists`.
- `WeilConjectures.relative_product_coefficient_factor_squares`.

No holes were added or split off. This is a partial proof delivery, not a
decomposition. The private helper is completely proved.

## No longer needed

None. No imports, nodes, modules or declarations were removed. The two untouched
statements still require their existing proof plan and dependencies. The proper
coordinate existence subargument itself only uses the given coordinate normalization,
A1 direct-image preservation, and Mathlib full-subcategory lifting; it does not need
an additional proper-coincidence or coefficient-reduction theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found in the subargument proved here. The supplied
A1 preservation fields apply directly, including to proper maps between spaces not
assumed separated over the base. No stronger separation hypothesis was introduced.
The main coefficient-square theorem and presentation existence are not claimed proved.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
