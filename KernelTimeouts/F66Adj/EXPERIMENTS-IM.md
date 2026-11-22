# Intrinsic vs mismatch-induced DefEq report

Case: `F66Adj`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, READY2-4.35.0.
Root: instantiated argument-39 counit proposition.
Branch baseline: `5ece8b` before this IM work.

## Variants and pairs

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. A transports only the `hR` proof representation; R restores the expensive `hR` form while changing the preceding tensor-isomorphism argument. A strict M cannot be constructed from the imported helper without changing its stored implicit provider, so no M timing is claimed.

## Kernel cost

Measured READY2 baselines: O 29.544 s, 3,897,905 calls, 15.058 s comparison, 14.486 s reduction, depth 121, 170,987,170 Expr constructions / 5,714,525,816 B. A entered no root over 100 ms (largest 26.484 ms, 2,881 calls). R returned 76.595 s, 9,536,477 calls, and 421,630,510 Expr constructions / 14,091,341,096 B. O had 176,636 Pi-domain events, 531,910 instantiations, and 1,290,616 exact repeats in the capped trace.

The trace root was 38.829 s. Its dominant inclusive path was nested `DFunLike.coe -> NatTrans.app`, with 34,886 ms in the deepest `.app` subtree; `tensorHomAdjunctionQhObj` and the derived monoidal proof were smaller children (2,026 ms and 1,899 ms).

## Operation and unification analysis

`DFunLike.coe`/`NatTrans.app` are path markers; the root partition is mixed dependent comparison and reduction. A removes the instantiated dependent proposition; R restores it. A tautological `Functor.obj` hint would be mechanical, so no unif_hint file is included: the source has no isolatable metavariable assignment that preserves argument 39 and its consumer.

## Conclusion

**H2 mismatch-induced, with descendant attribution.** The `hR` representation drives the measured tree; intrinsic `.app` cost is not established. A valid M would require a second non-identical counit proposition using the same provider, which is unavailable in the imported theorem.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs M): 170,987,170 / 2,872,049,664 B versus 34,551 / 5,177,344 B. These are process proxies, not retained allocations.

Revision for fresh runs: current-case source head `03f2a41973c`; oleans are the master `f21ef672d31` set plus later targeted Stability rebuilds. READY2-4.35.0. `probes/im/Matched.lean` is a **diagnostic M**: the concrete derived global-Hom counit `.app` is compared with the same counit applied to a beta-expanded copy of the same object. A local `have h` is consumed by `exact h`; its inferred and expected equality types are syntactically distinct. The provider, counit, and data-bearing derived-module type agree. O instead compares the instantiated argument-39 `hR` dependent proposition within `homIso_naturality_of_counit`; M changes that root obligation and omits its mismatched provider.

| Fresh READY2 counters | O | M, final `exact h` root | A | R |
|---|---:|---:|---:|---:|
| root wall / calls | 29,648.574 ms / 3,897,905 | 5.933 ms / 881 | no root >=100 ms | 29,366.396 ms / 3,901,014 |
| comparison / WHNF exclusive | 15,064.974 / 14,583.601 ms | 3.058 / 2.876 ms | no large root | 14,974.884 / 14,391.512 ms |
| depth / Expr proxy | 121 / 170,987,170 | 93 / 34,551 | - | 121 / fresh root proxy in log |

Fresh O branch exclusive: projection 832,323 calls / 9,320.076 ms; application 719,539 / 2,306.329 ms; second-WHNF 310,390 / 1,595.205 ms. M: projection 33 / 0.337 ms, application 115 / 0.546 ms, second-WHNF 149 / 1.289 ms. The fresh trace's O child chain is `CategoryStruct.comp -> DFunLike.coe -> NatTrans.app` (43,317 ms inclusive below the `DFunLike.coe` node, only 0.085 ms direct at that node). M enters `NatTrans.app -> CategoryStruct.comp -> DFunLike.coe` too (5.634, 5.286, 4.701 ms inclusive; 0.229, 0.044, 0.114 ms direct). Thus the operation heads are traversed in M, while O's many projection and application descendants are absent. The trace times are not interchangeable with counters times. The final uninstrumented M run was 2.83 s wall including import; O release time was not rerun separately.

**Verdict: diagnostic H2 support, strict H1/H2 classification inconclusive.** O/A/R establish that the original `hR` representation causes a large root; M establishes that one non-identical same-provider counit component comparison is cheap. Because M replaces the dependent `hR` consumer, its 4,424-fold call difference cannot isolate the intrinsic cost of that exact proposition. No applicable source-level `unif_hint` changes the already stored implicit provider in this imported theorem.
