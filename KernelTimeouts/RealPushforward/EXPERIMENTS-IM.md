# Intrinsic vs mismatch-induced DefEq report

Case: `RealPushforward`
Lean/Mathlib: Lean 4.35.0, current-case revision `a2ec460045b`, READY2-4.35.0.
Root: final polynomial equality conversion.
Branch baseline: `5ece8b` before this IM work.

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. A changes the declared polynomial representation to `charpolyRev`; R restores the original target. A is an alignment, not a matched control. No strict M preserves the original polynomial consumer with two non-identical matched inputs.

Measured READY2 O: 52.072 s, 17,340,236 calls, 52.069 s comparison, 0.0028 s reduction, depth 91, 281,349,193 Expr constructions / 9,142,377,040 B. A entered no root over 100 ms. The trace root was 68.258 s, dominated by `Matrix.charmatrix` through nested `DFunLike.coe` (68,253 ms); O had 3,545,728 exact repeats. R restores the timeout-scale root.

`Matrix.charmatrix`, `ContinuousMap`, and `DFunLike.coe` are descendants with inclusive path timing only. The polynomial alignment removes the trigger while a shallow semiring difference remains, so no claim is made that the whole downstream family is mismatch-only.

## Conclusion

**H3 interaction.** The polynomial mismatch is causal for entering the comparison-heavy path, while the matched intrinsic cost is not measured. The RealPurity trace has the same family and nearly the same footprint, supporting a shared operation family but not identical pair identity. No unif_hint is added because no isolatable metavariable/provider choice is present.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs M): 281,349,193 / 1,586,626,560 B versus 121 / 0 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, READY2-4.35.0, and master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` is a **diagnostic M** on `Matrix.charmatrix` over the same `PadicAlgCl l` field: `Matrix.charmatrix M` versus the same operation on eta-expanded `M`. Both inputs use one matrix provider; the `exact h` equality types are syntactically distinct, and READY2 recurses into `Matrix.charmatrix`. O instead compares concrete local Frobenius polynomials under the full realness consumer, which M omits.

| Fresh READY2 counters | O | M | A | R full replay |
|---|---:|---:|---:|---:|
| root wall / calls | 52,021.014 ms / 17,340,236 | 0.030 ms / 15 | no root >=100 ms | 53,627.687 ms / 17,340,236 |
| comparison / WHNF exclusive | 52,018.075 / 2.939 ms | 0.027 / 0.003 ms | no large root | 53,624.761 / 2.926 ms |
| max depth | 91 | 6 | - | 91 |

O has 10,902,868 failure calls / 45,333.568 ms comparison-exclusive and 1,430,775 lazy-delta calls / 5,644.525 ms; M has no failure calls and reaches `Matrix.charmatrix` for only 0.040 ms inclusive (0.023 ms direct exclusive in trace). O's `Matrix.charmatrix` path through `DFunLike.coe` is an inclusive child path, not an exclusive operation timer. The previous `Restored.lean` stops at `sorry` before `exact this`, so its cheap fresh run is invalid as R. `probes/im/RestoredRoot.lean` replays the complete original after A and restores the 17.34M-call timeout. Final M source run was 2.83 s wall including imports; no standalone O release timing was rerun.

**Verdict: diagnostic H2 support; strict matched-root verdict inconclusive.** A/R prove the polynomial alignment removes and restores the expensive root. The cheap same-provider characteristic-matrix eta conversion is a smaller obligation; its roughly 1.16M-fold call gap from O is not an isolated causal estimate for the original Frobenius input. The previous H3 label above was based on alignment alone and should not be read as a measured intrinsic M cost.
