# Intrinsic vs mismatch-induced DefEq report

Case: `RealPurity`
Lean/Mathlib: Lean 4.35.0, current-case revision `a2ec460045b`, READY2-4.35.0.
Root: final `exact h` in the rewritten `hreal'` proposition.
Branch baseline: `5ece8b` before this IM work.

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. A aligns both visible ring leaves; R aligns only the left ring leaf. Neither is a valid strict M because both preserve the downstream polynomial/object mismatch.

Measured READY2 O: 53.956 s, 17,310,168 calls, 53.949 s comparison, 0.0068 s reduction, depth 93, 280,888,851 Expr constructions / 9,127,445,872 B. A still timed out with the same comparison footprint. R/downstream diagnostic: 67.955 s and timeout. The trace root was 70.041 s; dominant path `DFunLike.coe -> Complex.re -> Matrix.charmatrix -> DFunLike.coe`, 70,033 ms. O had 3,545,573 exact repeats in the capped trace.

`Matrix.charmatrix` and `DFunLike.coe` are path markers; their exclusive branch times are not exposed. The ring leaf is a measured negative ablation. No genuine source-level unif_hint is available without changing the polynomial/provider expression.

## Conclusion

**H1 intrinsic downstream comparison plus H2 trigger, unresolved as a strict M.** The common comparison-heavy `ContinuousMap`/`DFunLike.coe` family remains after ring alignment; the exact ordered pair is not identified.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs M): 280,888,851 / 1,582,432,256 B versus 121 / 0 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, READY2-4.35.0, and master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` is a **diagnostic M** on the same characteristic-matrix operation and coefficient field `PadicAlgCl l`: `Matrix.charmatrix M` versus `Matrix.charmatrix (fun i j => M i j)` for one matrix provider. Its `exact h` requires a syntactically distinct equality type and READY2 reaches the `Matrix.charmatrix` child. O compares the polynomial/coercion expressions inside the lisse-sheaf realness proof, so M removes that consumer, its concrete Frobenius matrix, and the original representation difference.

| Fresh READY2 counters | O | M | A | R |
|---|---:|---:|---:|---:|
| dominant root wall / calls | 53,575.164 ms / 17,310,168 | 0.029 ms / 15 | 53,380.960 ms / 17,310,167 | 55,241.177 ms / 17,310,167 |
| comparison / WHNF exclusive | 53,567.848 / 7.315 ms | 0.026 / 0.003 ms | 53,374.125 / 6.834 ms | 55,234.632 / 6.545 ms |
| max depth | 93 | 6 | 93 | 93 |

O's failure branch is 10,883,715 calls / 46,715.874 ms comparison-exclusive; lazy delta is 1,428,285 / 5,781.654 ms. M has no failure branch: 11 quick, 1 application, 1 lazy-delta, and 2 eta calls. The M trace enters `Matrix.charmatrix` with 0.040 ms inclusive and 0.023 ms direct; the fresh O trace follows `DFunLike.coe -> Complex.re -> Matrix.charmatrix -> DFunLike.coe` (74,002.869 ms inclusive at `Matrix.charmatrix`, only 0.017 ms direct). O, A and R all hit Lean's deterministic timeout and the subsequent unknown-constant error. Final M source run was 2.36 s wall including import; no standalone O release timing was rerun.

**Verdict: inconclusive on intrinsic versus mismatch cost.** The ring-leaf alignment does not remove the 17.31M-call failure tree, while this matched eta comparison is cheap. The O/M obligations and matrix inputs are different, so H1 cannot be inferred from the persistent O/A cost and H2 cannot be inferred from the tiny M. `Matrix.charmatrix` itself has a small direct cost in M; O's expensive descendant remains to be isolated with a matched concrete Frobenius input.
