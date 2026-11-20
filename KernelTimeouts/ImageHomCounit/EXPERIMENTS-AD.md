# DefEq Internal Cost Experiments

Case: `ImageHomCounit`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: final `exact h` conversion for `conjugateEquiv_counit`.
Instrumentation: observational counters/trace build; round-two diagnostic controls.

## A1: Original root

Baseline root: `original.lean`. Counters measured 73.084 s, 6,359,958 recursive calls, maximum depth 204, 37.145 s comparison-exclusive and 35.939 s WHNF-exclusive. The trace sample had 1,644,449 exact repeats; sampled repeated immediate exclusive time was 0.686 s. Pi-domain events numbered 265,526 and proposition comparisons 121,496, with an overlapping proposition timer.

The workload is mixed, deep, and wide. The largest trace children include `Add.add`, `LinearMap.mk`, `AddCommGroup.toAddCommMonoid`, `HAdd.hAdd`, `DFunLike.coe`, and `ModuleCat.Hom._mkInternal`. Direct `Functor.obj` Delta timing was small compared with the root, so the high unfold count is not itself a causal timing claim.

## A2: Full endpoint alignment

Control: `aligned.lean`, aligning every raw/wrapper derived-category endpoint to the unchanged inferred type while retaining the same `h` and final exact consumer. The fresh diagnostic completed in 2.62 s (1.71 s user, 0.93 s system); the threshold-zero instrumented control's largest root was 16.251 ms and 2,881 calls. The elaborated pair changed as intended and the theorem obligation was preserved.

## A3: Wrapper-only restoration/control

Control/restoration: `restored-wrapper.lean`, expanding only the outer wrapper while leaving the inner mismatch. The diagnostic took 85.78 s wall (84.55 s user, 1.24 s system) and the counters root was 9,539,325 calls and 116.247 s, split 57.738 s comparison and 58.509 s WHNF. Restoring the fully raw target returns the original 54--56 s scale. This shows that wrapper exposure is not the whole cost; the inner endpoint bundle remains independently expensive.

## Conclusion

Full representation alignment is a valid A2 ablation: it removes the large comparison/reduction tree at the same consumer, and restoration returns it. Wrapper-only exposure is a negative control and is slower than the original, so no single outer wrapper field is claimed as the dominant child.

## READY2 round 2

The READY2-4.35.0 original root was 50.730 s with 6,359,958 calls, 25.076 s comparison-exclusive time, and 25.655 s reduction-exclusive time. Dependent comparison/reduction was 20.300 s / 20.236 s (79.9% of the root partition); 265,526 Pi-domain events and 825,116 instantiations were recorded. The Expr proxy created 281,230,787 expressions / 9,398,990,560 bytes, with a 4,752,474,112-byte RSS/commit delta.

The trace root was 62.200 s (22.6% overhead). The dominant path was the dependent endpoint's `Functor.map` -> `NatTrans.app` -> `DFunLike.coe` chain under `root/binder_body[6]/argument[1]`, with 62,183 ms in the deepest repeated `NatTrans.app` subtree. The restored raw target was 48.764 s with the same 6,359,958 calls and allocation count. The aligned target had only a 0.058 ms root and no Expr construction at that root, confirming that the complete endpoint bundle is the causal ablation.

The READY2 wrapper-only control also remained expensive: 75.453 s, 9,539,325 calls, 37.416 s comparison / 38.037 s reduction, and 421,726,792 Expr constructions / 14,094,527,488 bytes (7,244,742,656-byte RSS/commit delta). This control is therefore a negative isolation result for the outer wrapper.
