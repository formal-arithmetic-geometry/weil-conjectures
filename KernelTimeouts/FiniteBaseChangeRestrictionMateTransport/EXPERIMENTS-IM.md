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
