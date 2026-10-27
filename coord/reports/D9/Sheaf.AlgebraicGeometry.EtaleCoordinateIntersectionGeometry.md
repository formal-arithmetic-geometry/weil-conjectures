## What changed

Proved `AlgebraicGeometry.etale_coordinate_intersection_geometry` with its existing
signature and both coordinate-ideal definitions unchanged. All added helpers are
private and proved in the item module.

The proof identifies coordinate quotient stalks using the existing closed-immersion
kernel formula and the first isomorphism theorem, permutes selected parameter positions
to an initial segment, and applies the existing regular-parameter quotient theorem.
Regular local domains give reducedness by the stalk criterion. On an etale source,
the affine localization comparison gives dimension equality, and the unramified
maximal-ideal formula transports every parameter list. Residue-field injectivity
transports vanishing indices. The global-ideal pullback formula supplies the required
base-change isomorphism, after which the same coordinate quotient argument applies.

Added private proof imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`, and
`Mathlib.Data.List.FinRange`. Updated the item node's proof and dependencies to record
these existing implementations. No public import, statement, definition, instance or
other module changed; no change record or consumer adaptation is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.etale_coordinate_intersection_geometry`
(node `lem-trf-etale-coordinate-intersection-geometry`).

Zero holes remain in the item module; zero holes added; zero statements split off.
The six private helpers are fully proved. This is a proof, not a decomposition.

## No longer needed

Removed these private imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Ideal.Maps`
- `Mathlib.RingTheory.Localization.Basic`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.RingTheory.Unramified.LocalRing`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
- `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`

The first nine are redundant imports: the APIs actually used are supplied by the
retained statement imports and the private implementation imports. Removing them does
not claim to remove those Mathlib modules from the transitive import closure.

The proof does not need node `lem-pc-closed-subscheme-base-change-ideal-image` or its
module `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`:
`comap_ofIdealTop` already identifies the generated ideal, and `comapIso` identifies
its subscheme with the categorical pullback. Replaced that planned dependency with the
existing closed implementation `lem-pc-ideal-sheaf-comap-affine-extension`; removed
the obsolete top-level tool-use approval for the former node. No source declaration
is withdrawn, and other consumers may still need that module.

The proof also does not invoke the planned separate
`lem-weil-pbc-localization-at-prime-of-quotient` or
`lem-weil-pbc-lft-pointwise-criterion`: the proved stalk-kernel API packages the first
calculation, and Mathlib's etale-to-locally-finite-type instances package the second.
The explicit `def-sbc-locally-finite-presentation` proof dependency is likewise redundant.
The unit statement and its route remain unchanged; this is auxiliary coordinate algebra.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's longer affine reconstruction was
unnecessary because the adopted source library already provides `ker_stalkMap`,
`comap_ofIdealTop`, and `map_maximalIdeal_stalkMap` with the needed normalization.

Checked the empty subset, empty schemes/intersections and zero-dimensional stalks:
no construction assumes a point exists, the finite-set permutation includes the
empty selection, and the dimension and span equations include empty parameter lists.
The original distinct-position hypothesis and target signature are preserved.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
