## What changed

The item theorem is now proved from the exact-functor homology transport API.  The
proof imports the new derived-slice comparison module, obtains the comparison for
the layer and the coefficient-changed tensor model, and transports it through the
exact chart over-functor in every degree.  The item's DAG proof route now cites the
new split node.

The new module
`Sheaf.Paper.FiniteQuotientLayerTensorDerivedSliceComparison` records the unresolved
pre-homology derived-object comparison as one strictly simpler named theorem.  Its
proof is intentionally left for a follow-up worker.

## Proved and sorry left

Proved: `AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_derived_homology_comparison`.

Sorry left: `AlgebraicGeometry.Scheme.finiteQuotient_layer_tensor_derived_slice_comparison`,
recorded by node
`lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison`.

## No longer needed

The original planned direct use of the site-derived-tensor descent theorem is no
longer needed in the item's proof: it belongs to the split derived-slice theorem.
No statement imports were removed; the three original public imports remain needed
by the item's signature.

## Where the brief, the DAG or earlier work was wrong

The original item proof plan bundled the derived tensor balancing construction and
homology transport in one theorem, while the available declarations do not yet
state the required derived-object comparison.  Splitting that pre-homology step
makes the target proof a real exact-functor argument and leaves the missing
mathematics as a smaller theorem.

## New nodes

Added `lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-quotient-layer-tensor-derived-slice-comparison.json`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerTensorDerivedHomologyComparison": "cd8fe642a061f164759f4551d6f24652d2003a16", "Sheaf.Paper.FiniteQuotientLayerTensorDerivedSliceComparison": "170cb276077c410e8caf9bd89342a7cb7b83a902"}, "results": {"Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison": {"hash": "b21fe3d461e5020a8a54a36c398d26abf7649bb9", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T08:17:20+0800", "transitive": 0, "version": 1}
```

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
