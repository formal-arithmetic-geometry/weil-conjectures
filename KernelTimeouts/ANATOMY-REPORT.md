# KernelTimeouts DefEq Cost Anatomy

Lean 4.35.0 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; instrumented Kernel source checksum `8982321f70352a7c775c77e66e2f25dbf71ea9de7fe978fffb8f600862b7d566`. The seven case reports, immutable probes, release diagnostics, counters and detailed traces were generated from new runs on the built current-master library tree. No library file or Kernel source was edited in this worktree.

| Case | Root wall s | Comparison s | WHNF s | Calls | Max depth | Multi-child calls | Exact repeats / captured | Baseline RSS KB | Outcome |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| ImageHomCounit | 73.084 | 37.145 | 35.939 | 6,359,958 | 204 | 1,346,313 | 1,644,449 / 5,000,000 | 7522312 | F |
| EtaleHomComparisonReversedExact | 36.191 | 18.707 | 17.484 | 3,180,470 | 111 | 673,160 | 1,046,492 / 3,180,470 | 5552900 | F |
| FiniteBaseChangeRestrictionMateTransport | 813.972 | 813.896 | 0.076 | 239,340,712 | 87 | 11,255,747 | 3,534,109 / 5,000,000 | 23966284 | B |
| F66Adj | 44.174 | 22.801 | 21.373 | 3,897,905 | 121 | 833,071 | 1,290,616 / 3,897,905 | 5708728 | F |
| IntegralComparisonPullbackRealizationShifts | 110.020 | 68.656 | 41.363 | 9,426,253 | 183 | 1,986,478 | 1,781,432 / 5,000,000 | 8374520 | F |
| RealPurity | 64.277 | 64.267 | 0.010 | 17,340,901 | 93 | 815,335 | 3,545,573 / 5,000,000 | 5653788 | B (partial) |
| RealPushforward | 63.942 | 63.938 | 0.004 | 17,340,236 | 91 | 815,279 | 3,545,728 / 5,000,000 | 4759316 | B (partial) |

Across the seven selected root measurements, the counters-only partition is 1089.410 s comparison-exclusive (90.4%) and 116.250 s outer WHNF-exclusive (9.6%). This includes partial roots at deterministic heartbeat timeouts for RealPurity and RealPushforward. FiniteBaseChange alone contributes 813.896 s of comparison time. The table is not a whole-file or historical-case total.

## Workload shapes and required questions

- **Reduction-dominated (A):** none of these seven on the exclusive WHNF timer. ImageHomCounit, EtaleHom and F66Adj are near-even mixed workloads; IntegralComparison is comparison-leading mixed. Frequent `Functor.obj`, `NatTrans.app`, `PresheafOfModules.obj` and `Add.add` unfolds take much less *direct Delta time* than the root and do not establish expensive reduction by themselves.
- **Comparison-dominated (B):** FiniteBaseChange (239.34 million calls and 813.896 s comparison), RealPurity (17.34 million and 64.267 s before timeout), RealPushforward (17.34 million and 63.938 s before timeout). RealPushforward contradicts the proposed shallow reduction-dominated negative-control signature.
- **Dependent/proof-type (C):** EtaleHom binder 26, FiniteBaseChange binder 49 and F66Adj binder 39 are located in instantiated proof propositions, but the inclusive proposition timer overlaps and cannot establish dominance. RealPurity and RealPushforward compare proof propositions at final handoffs, yet their measured main cost is a huge comparison tree.
- **Repeated work (D):** all trace roots have exact repeated-pair entries. For the three comparison-dominated roots, the first 5 million calls contain about 3.53-3.55 million repeats, but sampled repeated-call exclusive time is a small fraction of each trace root. Repetition is frequent, not established as the main time expense.
- **Allocation/memory (E):** not classifiable. Process RSS reaches 23,966,284 KB in the FiniteBaseChange release diagnostic and 35,101,408 KB in its trace, but the patch has no Expr allocation or GC accounting.
- **Mixed (F), depth and width:** ImageHomCounit (depth 204), EtaleHom (111), F66Adj (121), and IntegralComparison (183) have large comparison trees with material multi-child fan-out. RealPurity/RealPushforward are comparatively narrow and share nearly identical `ContinuousMap`/`DFunLike.coe` trace-head patterns.

## Measurement limits

The root exclusive partition covers comparison and outer WHNF as implemented in this patch. Direct Delta timers and the proposition timer overlap that partition; proposition time can exceed root wall and must not be summed. Beta/Iota/Zeta/projection times, per-argument/field paths, top repeated pair groups, local-context fingerprints, reversed pairs, Expr allocation, GC, and reliable phase-specific peak memory were not emitted. Trace top-child times may include instrumentation bookkeeping. Controls with sub-100-ms conversions were rerun at a zero report threshold, which reports many unrelated roots; their reported maximum is an upper bound, not a paired conversion ID. The separate historical-case reports state that their exact old dependency closure was unavailable, so no measured 4.33.1 internal signature exists for cross-version comparison.
