## What changed

Added the proof-only ambient contraction module and the restricted-to-ambient transport module. The item theorem now applies the transport factorization and then the ambient contraction theorem. The item imports these modules privately; the original public statement and hypotheses are unchanged.

## Proved and sorry left

The item theorem `integralKernel_first_contraction` is proved by composition of the two split interfaces. Two strictly smaller statements remain as named sorries: `integralKernel_first_transport` in `lem-integral-kernel-first-transport`, and `integralKernel_first_ambient_formula` in `lem-integral-kernel-first-ambient-formula`.

## No longer needed

The item proof no longer directly imports or cites the three original proof-dependency modules; they are retained as dependencies of the ambient split theorem. No existing library module or declaration was pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled restricted-category transport with the integral ambient trace/base-change calculation. The integral coefficient ring is the padic integer ring, while the existing rational ambient contraction theorem is parameterized by a different coefficient ring, so it cannot close this item directly. The route was therefore split into the two strictly smaller interfaces above.

## New nodes

`lem-integral-kernel-first-transport` records the formal normalization transport. `lem-integral-kernel-first-ambient-formula` records the ambient geometric contraction and retains the original trace/base-change, diagonal-coefficient, and projection-section dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralKernelFirstAmbientFormula": "456d1456e7fda7321c8f7c050ee258c1c19647f9", "Sheaf.SixFunctors.IntegralKernelFirstContraction": "6df44a0fdfe6464a389e88905bace36b87ee6be8", "Sheaf.SixFunctors.IntegralKernelFirstTransport": "56a3d2f1272a1525fa724b523bcf8d796f55a1cf"}, "results": {}, "time": "2026-10-28T04:18:56+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
