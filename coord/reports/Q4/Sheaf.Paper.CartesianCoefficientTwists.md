## What changed

Proved `AlgebraicGeometry.ProEtale.spIntegralComparison_existsUnique` in
`Sheaf.Paper.CartesianCoefficientTwists`. The finite-level tensor comparisons form
an actual natural transformation, using naturality of the coefficient comparison
and the existing Kummer transition square. The module forgetful functor preserves
the target limit, so its universal property supplies existence and uniqueness.

The finite-level map and its natural transformation are private concrete definitions,
with a proved component formula. Keeping that formula in terms of the named map
prevents costly kernel expansion of the inverse-image tensor construction when
normalizing opposite-category indices. A proved private general limit lemma handles
the universal property. All public signatures and definitions remain unchanged.

Removed the redundant direct proof import
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.

## Proved and sorry left

Closed 1 of the original 6 holes:
`AlgebraicGeometry.ProEtale.spIntegralComparison_existsUnique`.
Added 0 holes; no split-offs.

The following 5 original holes remain unchanged, all attached to
`det-prop-sfb-cartesian-coefficients-twists`:

- `AlgebraicGeometry.ProEtale.spRoots_cartesian`.
- `AlgebraicGeometry.ProEtale.spCoefficientIso_existsUnique`.
- `AlgebraicGeometry.ProEtale.spRationalComparison_existsUnique`.
- `AlgebraicGeometry.ProEtale.spFiniteTwists_cartesian`.
- `AlgebraicGeometry.ProEtale.spTwists_cartesian`.

The proved integral existence theorem still uses the stated finite-level transition
normalizations and roots-of-unity transition compatibility. It does not assert that
inverse image preserves arbitrary inverse limits.

## No longer needed

Removed the redundant direct import
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`; its coefficient
constructions remain available through the statement imports. No DAG node or
module is pruned from the remaining theorem plans. Other existing imports support
the five unchanged obligations, whose stated proof routes are retained.

## Where the brief, the DAG or earlier work was wrong

The retained proof from the interrupted attempt timed out in kernel checking.
The issue was expansion of the concrete finite-level comparison while reducing
opposite-category indices. Named concrete comparison definitions and a component
formula with the named map fix this; the complete item compiles in 9.9 seconds.
No mathematical statement or blueprint route was changed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
