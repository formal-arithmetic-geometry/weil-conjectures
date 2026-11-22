# Intrinsic vs mismatch-induced DefEq report

Case: `FiniteBaseChangeRestrictionMateTransport`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, matching the READY2-4.35.0 kernel.
Root: dependent argument `hb` (argument 49), the `Site`/`Quiver.Hom` proposition.
Branch baseline: `5ece8b` before this IM work.

## Variants and expression pairs

- **O Original:** `probes/im/Original.lean`, the original `transport_from_unit` application with the concrete `hb` proposition.
- **A Aligned:** `probes/im/Aligned.lean`, whole-proposition transport, preserving the consumer and dependent telescope.
- **R Restored:** `probes/im/Restored.lean`, the original proposition restored after the transport control.
- **M Matched:** `probes/im/MatchedLet.lean` is a diagnostic attempt only. It adds a reducible wrapper to one endpoint, but the strict root still contains the original `Site .ordinary` versus `ProEt` divergence. It was not counted as M.

The O/A/R pair audits are inherited from the immutable head audit: O and R retain the raw/abbrev divergence; A changes the expected proposition to a definitionally equal transported proposition. The matched attempt therefore does not satisfy the M definition.

## Kernel cost

The O/A/R figures below are measured READY2-4.35.0 AD baselines from the same probe snapshots (reused rather than rerun because O reaches multi-hundred-second and multi-GB scale).

| Variant | Root time | DefEq calls | Comparison excl. | WHNF excl. | Max depth | Expr proxy |
|---|---:|---:|---:|---:|---:|---:|
| O | 661.952 s | 239,340,712 | 661.896 s | 0.0559 s | 87 | 2,960,140,990 / 96,645,705,328 B |
| M | invalid | - | - | - | - | strict mismatch remains |
| A | no root >100 ms; setup 0.116 s | 678,893 setup | - | - | - | 678,893 setup |
| R | 646.663 s | 239,340,717 | 646.607 s | 0.056 s | 87 | 2,960,142,822 / 96,645,767,016 B |

O had 686 Pi-domain events, 40,293,390 instantiations, and 3,534,109 repeated exact entries in the capped trace. The trace root was 776.225 s; the deepest path was `CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app`, with 776,096 ms and 239,324,175 calls in the deepest repeated subtree. These timers are inclusive path samples; they are not branch-exclusive attribution.

## Operation analysis

The `CategoryStruct.comp`/`LinearMap.comp` nodes are path markers. The measured exclusive root is the dependent proposition comparison; `NatTrans.app` is reached repeatedly below it. WHNF is negligible, so the dominant mechanism is recursive comparison, not reduction. Exact pair repetition is frequent, but sampled repeated immediate time is only 6.144 s and does not establish repetition as the main cost.

`unif_hint`: `probes/im/UnifHint.lean` declares the genuine `Site .ordinary X ≟ X.ProEt` hint. It typechecks with Kernel checking skipped. No U1 Kernel profile is claimed: the mismatch is entered after elaboration, and applying the hint to the stored theorem would change the source-level provider rather than hold the root fixed.

## Conclusion

**H2 mismatch-induced, with no measured intrinsic M.** Directly measured: O/R comparison work and A removal of the expensive root. Inferred: the Site/ProEt divergence is the causal trigger because A preserves the consumer and removes the tree. The next falsifying control would be a valid same-provider, non-identical `CategoryStruct.comp` pair with the exact `hb` obligation; the current theorem does not expose one.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs M): 2,960,140,990 / 22,056,599,552 B versus 34,418 / 393,216 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, Lean/READY2-4.35.0, and master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` is a **diagnostic M** with the concrete left-hand composite from the finite mate square on both sides: `e.pullU_pin.ordinary.hom.app ((ProEtale.upperStar ... j).obj N) ≫ o.gUPull.ordinary.map (...) ≫ o.ordinaryTheta.inv.app (...)`, versus the same composite with only the first `.app` object's beta-expanded spelling. Both sides share `e`, `o`, the Site/ProEt provider, and the module type; `exact h` consumes syntactically different equality types. READY2 descends through two `CategoryStruct.comp` nodes. O instead checks argument-49 `hb` in the full `transport_from_unit` telescope, which M replaces with a local component equality.

| Fresh READY2 counters | O | M | A | R full replay |
|---|---:|---:|---:|---|
| root wall / calls | 612,036.328 ms / 239,340,712 | 4.627 ms / 640 | no expensive `hb` root; setup root 113.650 ms / 19,783 | 625,693.965 ms / 239,340,712 |
| comparison / WHNF exclusive | 611,979.762 / 56.566 ms | 3.698 / 0.929 ms | setup 75.336 / 38.314 ms | 625,641.277 / 52.688 ms |
| max depth | 87 | 33 | setup 64 | 87 |

O has 150,477,480 failure calls / 519,110.383 ms comparison-exclusive, 19,747,209 lazy-delta calls / 77,753.399 ms, and 68,971,032 quick calls / 13,501.339 ms. M has no failure branch: 108 projections / 1.461 ms, 85 applications / 0.843 ms, and 401 quick calls / 1.023 ms. The M trace's two `CategoryStruct.comp` nodes cost 4.606 and 4.567 ms inclusive but only 0.031 and 0.041 ms direct exclusive. Fresh O trace follows `CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app`; those latter three nodes carry 778,689.112 / 778,683.265 / 778,682.999 ms inclusive, but only 0.035 / 0.121 / 0.378 ms direct exclusive. `Restored.lean` from Round 1 is only a Site-equality smoke test and has no root. `RestoredRoot.lean` replays the complete original after A. Final M source run was 2.54 s wall including imports; no separate O release run was made.

The Round 2 `unif_hint` U0/U1 argument audits (`probes/im/{OriginalAudit,UnifHintAudit}.lean`) select binder 49 and show identical pretty-printed actual and expected `hb` propositions, including the first `ProEt` versus `Site` divergence; their normalized audit excerpts have the same SHA-256 digest `695947a17c9ebb043bf4449d783c07a1f4c5a89a5a18c39c8b7d317e39ce382a`. Raw `Expr.hash` values differ because fresh variable IDs differ across files, and do not indicate a changed pair. Fresh **full kernel checking** of `probes/im/UnifHint.lean` exited successfully with the same 239,340,712 calls, 150,477,480 failure-branch calls, and 19,747,209 lazy-delta calls as U0; its root was 632,767.536 ms (632,715.238 comparison-exclusive, 52.299 WHNF-exclusive). That 3.4% wall difference is consistent with run noise and does not show a kernel improvement. U2 has no distinct provider to fix because U1 did not change the elaborated pair. U0/U1 audit elaboration took 4.59/4.58 s wall; unification-attempt and metavariable-assignment counters are unavailable in this setup.

**Verdict: diagnostic H2 support; strict intrinsic-versus-mismatch classification inconclusive.** A removes the enormous `hb` root, R restores it, and the same-provider composite M is cheap, but M does not preserve the dependent argument-49 obligation. The 374,000-fold O/M call gap measures those different obligations as well as the representation difference; it cannot alone allocate the cause.
