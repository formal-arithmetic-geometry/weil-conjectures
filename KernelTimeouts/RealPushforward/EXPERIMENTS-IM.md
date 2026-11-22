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
