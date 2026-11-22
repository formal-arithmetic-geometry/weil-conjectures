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
