# DefEq Internal Cost Experiments

Case: `RealPurity`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: final `exact h` in the rewritten `hreal'` proposition.
Instrumentation: observational counters/trace build; downstream diagnostics.

## A1: Original root

Baseline root: `original.lean`. The deterministic timeout stopped the counters root at 64.277 s: 17,340,901 recursive calls, 4,977,891 successful and 12,363,010 failed/stuck, maximum depth 93, 64.267 s comparison-exclusive and 0.010 s WHNF-exclusive. The trace sample contained 3,545,573 exact repeats and 10.206 s sampled repeated immediate exclusive time. Top children are `DFunLike.coe`, `ContinuousMap.proj` versus `Function.comp`, `ContinuousMap.comp`, and `Eq.ndrec`.

## A2: Ring-leaf alignment

Control: `aligned-both-ring.lean`, aligning both visible ring leaves while keeping the exact proof consumer. The timeout remained: 63.831 s and 17,340,901 calls, with 12,363,010 failures. Left-only alignment also retained the same call count. This is a valid negative ablation of the measured first leaf, and it rejects that leaf as the dominant component.

## A3: Downstream diagnostic and shared-hotspot check

`downstream-ring.diagnostics.stderr` records the post-ring diagnostic run: 66.01 s wall, 61.95 s user, 1.36 s system, 5,579,280 KB RSS, deterministic timeout. It moves the first visible difference to `Functor.obj` versus local `P` under `LinearMap.charpoly`; the diagnostic footprint includes `DFunLike.coe`, `Functor.obj`, `ContinuousMap.toFun`, and `LinearMap.charpoly`.

The RealPushforward trace has the same `ContinuousMap`/`DFunLike.coe` family and nearly identical partial-root counters (17,340,236 calls, 63.938 s comparison, depth 91). Thus the shared expensive sub-comparison is established at the expression-head family level, not as one exact node: the patch lacks context-aware pair identity and field paths. A raised-budget diagnostic (`maxHeartbeats 400000`) ran for 118.17 s wall (117.16 s user, 7,183,580 KB RSS), still timed out, and then produced the expected unknown-constant cascade from the failed private theorem. It is retained as a diagnostic, not as a completed root measurement.

## Conclusion

The ring instance is not the dominant component. Both cases share a downstream `ContinuousMap`/`DFunLike.coe` comparison family after the polynomial/object boundary; the exact semantic pair and allocation cost remain unknown.

## READY2 round 2

The READY2-4.35.0 original expensive root was 53.956 s with 17,310,168 calls, 53.949 s comparison-exclusive time, and 6.767 ms reduction-exclusive time. Dependent comparison/reduction was 53.757 s / 4.653 ms; 2,914,290 instantiations were recorded. The Expr proxy created 280,888,851 expressions / 9,127,445,872 bytes, with a 1,582,170,112-byte RSS/commit delta. The raised downstream diagnostic root was 67.955 s with the same comparison-dominated shape and 280,888,851 Expr constructions.

The READY2 trace root was 70.041 s (29.8% overhead). Its dominant path was `DFunLike.coe` -> `Complex.re` -> `Matrix.charmatrix` -> nested `DFunLike.coe`, with the deepest `DFunLike.coe` subtree at 70,033 ms. Ring-leaf alignment still entered no comparable expensive root; the later diagnostic timeout and unknown-constant cascade are retained as an incomplete diagnostic, not a theorem result.
