# DefEq Internal Cost Experiments

Case: `RealPushforward`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: final `exact this` polynomial equality conversion.
Instrumentation: observational counters/trace build; aligned diagnostic control.

## A1: Original root

Baseline root: `original.lean`. The deterministic timeout stopped the counters root at 63.942 s: 17,340,236 calls, 4,977,433 successful and 12,362,803 failed/stuck, maximum depth 91, 63.938 s comparison-exclusive and 0.004 s WHNF-exclusive. The trace sample had 3,545,728 exact repeats and 10.160 s sampled repeated immediate exclusive time. The largest children are `DFunLike.coe`, `ContinuousMap.proj` versus `Function.comp`, `ContinuousMap.comp`, and `Eq.ndrec`.

## A2: Polynomial representation alignment

Control: `aligned.lean`, changing only the definitionally equal declared polynomial representation to `charpolyRev` while retaining the same final consumer. The fresh diagnostic completed in 3.21 s (2.03 s user; 3,178,928 KB RSS). The aligned pair still has a small semiring-instance difference, but no large root remains. The original pair is restored by `original.lean` and returns the timeout.

## C cross-case comparison

The RealPurity and RealPushforward traces share the same post-polynomial head family: `DFunLike.coe` and `ContinuousMap` projections at depths 82--86, followed by `Eq.ndrec` and category composition. Their partial roots differ by less than 0.4 s and about 665 calls. This is evidence for one shared expensive sub-comparison family, not proof that the exact ordered expression pair is identical; local context and complete pair paths are unavailable.

## Conclusion

The polynomial-head mismatch is a causal A2 trigger, but the expensive partial roots are comparison-dominated after that representation is exposed. The negative control leaves a shallow semiring mismatch, so the remaining timeout is not explained by the semiring leaf alone.

## READY2 round 2

The READY2-4.35.0 original root was 52.072 s with 17,340,236 calls, 52.069 s comparison-exclusive time, and 2.805 ms reduction-exclusive time. Dependent comparison/reduction was 51.883 s / 2.542 ms; 2,919,416 instantiations were recorded. The Expr proxy created 281,349,193 expressions / 9,142,377,040 bytes, with a 1,586,626,560-byte RSS/commit delta.

The detailed trace root was 68.258 s (31.1% overhead). Its dominant path was `Matrix.charmatrix` through nested `DFunLike.coe`; the deepest repeated `DFunLike.coe` subtree carried 68,253 ms. Polynomial alignment entered no root over 100 ms (3,210,288 KB RSS), while the original trace retained the comparison-heavy root. The RealPurity and RealPushforward traces therefore share the same measured `ContinuousMap`/`DFunLike.coe` style of downstream work, without claiming one identical ordered pair.
