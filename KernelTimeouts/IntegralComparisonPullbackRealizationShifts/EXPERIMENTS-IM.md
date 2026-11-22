# Intrinsic vs mismatch-induced DefEq report

Case: `IntegralComparisonPullbackRealizationShifts`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, READY2-4.35.0.
Root: downstream `change` conversion after `commShift_of_localization` and `intro P m`.
Branch baseline: `5ece8b` before this IM work.

## Variants and cost

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. The aligned control changes only the first visible instance path; it is intentionally a negative control because the downstream endpoint remains mismatched. A strict M is unavailable: the first instance is not the root and replacing it does not preserve the complete declared endpoint.

Measured READY2 O: 73.839 s, 9,426,253 calls, 44.816 s comparison, 29.024 s reduction, depth 183, 438,986,428 Expr constructions / 14,632,433,896 B. A/first-instance diagnostic: 88.99 s wall and still expensive; no ablation. R/downstream trace: 88.313 s, with the same 9,426,253-call root and a 46,686 ms repeated `NatTrans.app` descendant. O had 1,781,432 exact repeats in the capped trace.

## Operation analysis

The dominant inclusive path is nested `CategoryStruct.comp -> NatTrans.app`; the first instance leaf is not causal. The operation branch’s exclusive time is unavailable, so `.app` is a path marker. No genuine unif_hint is added: the imported endpoint has fixed providers, and a hint would alter the `change` target.

## Conclusion

**H3 interaction / unresolved mismatch.** The matched first-leaf control remains expensive, showing that the downstream composition has intrinsic cost; the original representation still amplifies it. A valid matched endpoint pair is required before separating H1 from H2.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (actual O vs M): 438,986,428 / 5,417,074,688 B versus 9,468 / 0 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, READY2-4.35.0, and master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` supplies a **diagnostic M** with the concrete `M.realization.hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _` versus the same composite at `DerivedCategory.Q.obj ((fun Z => Z) P)`. Both sides use the same realization provider, `NatTrans.app`, `Functor.obj`, and `CategoryStruct.comp`; `exact h` consumes syntactically different equality types and the kernel recurses. O is the much larger downstream `cancel_shift_square` application, so M removes its dependent arguments and changes the root obligation.

| Fresh READY2 counters | O, actual downstream site | M | A, first-instance alignment | R |
|---|---:|---:|---:|---|
| root wall / calls | 73,266.756 ms / 9,426,253 | 0.729 ms / 54 | 72,856.760 ms / 9,426,253 | 73,107.446 ms / 9,426,237 |
| comparison / WHNF exclusive | 44,602.554 / 28,664.202 ms | 0.146 / 0.583 ms | 44,446.676 / 28,410.084 ms | 44,551.528 / 28,555.918 ms |
| max depth | 183 | 16 | 183 | 183 |

O has 2,096,326 projection calls / 26,926.832 ms comparison-exclusive, 1,664,481 application calls / 10,190.288 ms, and 481,421 second-WHNF calls / 2,911.620 ms. M has 9 applications / 0.030 ms and 9 second-WHNF calls / 0.019 ms; its trace reaches `NatTrans.app`, `CategoryStruct.comp`, and `Functor.obj` as small descendants. The fresh O trace goes through `CategoryStruct.comp -> NatTrans.app -> NatTrans.app` (88,003 / 88,003 / 88,003 ms inclusive, but only 0.023 / 0.185 / 0.060 ms direct). These are inclusive paths, not per-operation exclusive timers. Final M source run was 2.60 s wall including imports; no separate O release run was made.

`probes/im/Original.lean` ends the relevant theorem with `sorry` before the expensive downstream application. Its fresh largest root is only 1,536.466 ms / 235,750 calls and must not be used as O. The actual O row above comes from fresh `probes/sa/r2/DownstreamInstance.lean`, the exact site used in the prior AD phase. `probes/im/Restored.lean` initially failed to import `HeadAuditTools`; after compiling that audit helper outside the read-only current tree and adding it to `LEAN_PATH`, the fresh R run returned the 9.426M-call root shown above.

**Verdict: inconclusive H1/H2, with an H3-style downstream persistence observation.** M is cheap but has a smaller consumer; O and A have the same 9.426M-call tree, so the first instance leaf is not its trigger. The intrinsic cost of a fully matched `cancel_shift_square` dependent argument remains unmeasured.
