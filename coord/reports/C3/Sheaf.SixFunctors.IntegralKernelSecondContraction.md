## What changed

Proved `integralKernel_second_contraction` by applying the strictly simpler transported
second-contraction statement and cancelling the canonical ambient twist isomorphism.
Added `Sheaf.SixFunctors.IntegralKernelSecondContractionPostcomp` and its DAG node for the
remaining geometric transport calculation.

## Proved and sorry left

Closed the `integralKernel_second_contraction` sorry. The new theorem
`integralKernel_second_contraction_postcomp` remains one sorry, split off as the ambient
transport substep described by node `lem-integral-kernel-second-contraction-postcomp`.

## No longer needed

None. The proof uses the existing unit-counit and normalized-family imports and the new
transport substep; no planned imports were pruned.

## Where the brief, the DAG or earlier work was wrong

The available completed declarations provide the integral unit and counit normalizations
separately, while the rational projective-line contraction theorem is specialized to the
rational coefficient object and cannot be instantiated at the integral coefficient. The
remaining integral transport calculation therefore has to be stated as a separate
postcomposition theorem; the original target follows by cancellation because the ambient
twist comparison is an isomorphism.

## New nodes

- `lem-integral-kernel-second-contraction-postcomp` in
  `dag/nodes/sec-six-functors-basics/lem-integral-kernel-second-contraction-postcomp.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralKernelSecondContraction": "9afd502e3a7846b31488050e250cb3ae0856489f", "Sheaf.SixFunctors.IntegralKernelSecondContractionPostcomp": "18abbf37005c1fef052a625cc00bff358256e38b"}, "results": {}, "time": "2026-10-28T04:29:45+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
