## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_trivialization_over_preimage_of_isFinite`
in `Sheaf.AlgebraicGeometry.FiniteTrivializeInvertibleUpstairs`, with its signature unchanged.
Added the private proof import `Sheaf.AlgebraicGeometry.AffineInvertibleFiniteSetSection`.
The proof follows Stacks 0BUT: choose an affine inverse image, use the stated section
nonvanishing on its finite fibre, trivialize on its nonvanishing open, and shrink by
removing the closed image of the complement. The shrinking takes place directly in the
original target. The final isomorphism uses the open-immersion lift and the restriction,
pullback-composition, and pullback-unit comparisons. Updated the item's proof record to
match this implementation. No other module, statement, or definition is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_trivialization_over_preimage_of_isFinite`
(node `lem-sfb-finite-trivialize-invertible-upstairs`). No holes left in the delivered
module; zero holes added or split off. The imported, already stated
`AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishing_on_finite_set`
(node `lem-sfb-affine-invertible-finite-set-section`) remains an existing dependency
with `sorry`; it is not changed or claimed proved by this delivery.

## No longer needed

None. Every declared mathematical proof dependency is used. All original imports stay:
`Proper` supplies closedness of finite maps, `QuasiFinite` supplies finite fibres, and
`NonvanishingSectionTrivializes` supplies the trivializing open and unique coefficients.
No nodes or modules are withdrawn or pruned; the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's separate finite restricted morphism and its
neighbourhood-to-original-target transport are unnecessary bookkeeping: after constructing
an open of Y containing the original fibre, closedness of p gives the neighbourhood
in Z directly. The proof record describes this variant. Empty fibres and nonclosed
fibre points require no additional hypotheses. No new nodes or interface changes.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
