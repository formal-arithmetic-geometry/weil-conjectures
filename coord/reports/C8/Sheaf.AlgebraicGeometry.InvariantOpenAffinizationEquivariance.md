## What changed

Proved both theorems in `lean/Sheaf/AlgebraicGeometry/InvariantOpenAffinizationEquivariance.lean`.
The original definitions and all public declaration signatures are unchanged.
Added proved private helpers for restriction naturality, the canonical pullback square,
tensor pushouts, affine-chart coordinates, and descent overlap calculations.
Added private imports of Mathlib ring constructions and pullback carriers; retained the
existing private imports actually used for the canonical embedding and inverse-image stalks.
Updated the item's node proof metadata to record its use of the existing
`lem-a1-invariant-intersection-affine-descent` and the direct pullback-range argument.

## Proved and sorry left

Closed the original two holes:

- `AlgebraicGeometry.invariant_open_affinization_flat_comparison`.
- `AlgebraicGeometry.invariant_open_affinization_equivariance`.

Zero `sorry`s remain in the item. Zero holes were added; zero statements were split off.
The proofs use the existing canonical-embedding, flat-section-comparison, and
invariant-intersection-affine-descent declarations, as intended by stage 3.
Every newly introduced private theorem is proved, and every private definition is
constructed explicitly. The full single-file compile completed successfully in 37.4 seconds.

## No longer needed

No Lean modules were withdrawn and no original imports were removed. Every added import
is used. The direct proof dependency and tool-use entry
`lem-weil-pbc-open-immersion-base-change` is removed from this node: the canonical map on W
is already open by the canonical-embedding theorem, while the asserted comparison square
and image equality follow directly from pullback universal properties and
`Scheme.Pullback.range_fst`. This is a removal of this item's direct dependency, not a
withdrawal of the Mathlib leaf or of any other node's dependency on it.
The remaining declared proof dependencies are used, including the Mathlib affine
adjunction and tensor universal-property leaves. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item node did not list the existing invariant-intersection affine-descent theorem
among its proof dependencies, although its final step needs the canonical section
isomorphism and affine datum provided there. This delivery records that dependency.
No false statement or definition repair was needed. Empty W, empty intersections,
and zero tensor rings require no exceptional argument: the proof uses universal
properties and open-immersion factorization without choosing points.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
