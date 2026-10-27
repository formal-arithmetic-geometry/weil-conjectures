## What changed

Added `Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore` with the split-off representative short-exact-sequence theorem. The item theorem now applies `DerivedCategory.triangleOfSES` and `triangleOfSES_distinguished`, transporting the three endpoint comparisons.

## Proved and sorry left

The item theorem `AlgebraicGeometry.Scheme.finiteQuotient_coefficient_layer_triangle` is proved. One strictly simpler obligation remains as `AlgebraicGeometry.Scheme.finiteQuotient_coefficient_layer_core` (`lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core`).

## No longer needed

No imports or declared dependencies were pruned beyond replacing the item's direct proof route with the split-off core theorem.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the representative construction and triangle transport into one theorem. The representative construction is a separate, strictly simpler short-exact-sequence obligation; the item now records this decomposition.

## New nodes

`lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core` is added for the representative short exact sequence and its three endpoint comparisons.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientCoefficientLayerTriangle": "4e692e97fefba22a6dee62cf67c9d17815ecd73a", "Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore": "e9b68954b02ddb6490d06e819a31d75628673ddc"}, "results": {}, "time": "2026-10-27T23:39:17+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
