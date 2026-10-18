## What changed

Proved `AlgebraicGeometry.Etale.isZero_universalCurveTest_higherDirectImage` in the item module. The proof constructs a `CurveTestDatum` from the explicit affine normal-base hypotheses, using the fraction-field equivalence between `A` and the scheme function field, and converts the chosen Cartesian square to the datum orientation. It normalizes the signed integer coefficient to `d.natAbs`, then applies the existing cyclic local-vanishing theorem. Degree one uses the existing `CurveTestDatum.exists_cover_cohomologyMap_eq_zero`; degrees at least two use the affine smooth-curve cohomology bound. The direct imports were pruned to the source vanishing interface and the cyclic local-vanishing interface.

## Proved and sorry left

Closed the sole item hole: `AlgebraicGeometry.Etale.isZero_universalCurveTest_higherDirectImage`. No `sorry` remains in the delivered module, and no new theorem or `sorry` was added.

## No longer needed

Removed the former direct imports of the presheaf implementation, affine-curve implementation, smooth-curve invariance, connected-coproduct assembly, Galois-category implementation, torsor/fibre-degree implementation, slicing implementation, and related low-level Mathlib/Weil imports. Their declarations are reached transitively by the two interfaces actually used. The old top-level presheaf `tool_uses` entry is obsolete because the proof calls the proved local-vanishing interface directly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expanded the complete Stacks argument inline, although the source library already packages the degree-one and cyclic-local-vanishing steps. The source orientation is `IsPullback e h (Spec.map i ≫ fromSpecStalk) f`; the chosen square is converted explicitly rather than identifying these structures definitionally. No statement or definition was changed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
