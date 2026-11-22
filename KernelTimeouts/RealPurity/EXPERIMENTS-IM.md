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
