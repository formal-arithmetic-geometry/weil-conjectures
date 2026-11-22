# KernelTimeouts intrinsic-versus-mismatch synthesis

Branch: `dataset/kernel-timeouts`, commit `fe11150bfa1`.
Current-case revision used for the IM probes: `a2ec460045b`.
The O/A/R measurements below are the immutable READY2-4.35.0 AD profiles recorded in each case report; the reports identify them as reused baselines. The Image matched diagnostic was rerun in this phase.

| Operation family | Matched M | Original O | Aligned A | Restored R | Exclusive owner | Verdict |
|---|---|---|---|---|---|---|
| `NatTrans.app` / endpoint components | strict M unavailable; Image diagnostic retained raw/abbrev mismatch | Image 50.730 s / 6.360M calls; Finite 661.952 s / 239.341M | Image no root >100 ms; Finite setup only | Image wrapper-only 75.453 s; Finite 646.663 s | dependent endpoint/`NatTrans.app` descendants | H2 for endpoint bundle; H3 where downstream composition remains |
| `DFunLike.coe` | no fixed-provider non-identical M | F66 29.544 s; Etale 24.140 s | both no root >100 ms | F66 76.595 s; Etale 81.640 s | nested `.app`/dependent proposition descendants | H2; operation itself not isolated |
| `Functor.obj` / `Functor.map` | no valid M or shared-provider replay | Image 6.360M calls; Ordered 18.945M | Image endpoint alignment; Ordered all-route alignment | Ordered domain restore ~35.939 s | `Quiver.Hom`/dependent `Exists` path and endpoint bundle | H2/H3 bundle interaction |
| `CategoryStruct.comp` / `LinearMap.comp` | no same-root M | Finite 239.341M calls; Integral 9.426M | Finite removes root; Integral first-leaf alignment remains costly | Finite restores; Integral downstream 73.839 s | nested composition into `.app` | H3 for Integral; H2 for Finite |
| `Matrix.charmatrix` | no strict polynomial M | RealPurity 53.956 s; RealPushforward 52.072 s | ring alignment negative for Purity; polynomial alignment removes Pushforward root | original timeout-scale profiles return | `DFunLike.coe`/`ContinuousMap` descendants | H1 downstream family plus H2 trigger; exact pair unresolved |
| dependent propositions/generated fields | no valid M preserving stored providers | F66/Etale/Finite roots above | whole-proposition transport removes root | restored roots return | dependent comparison, not WHNF | H2 strongly supported |

## `unif_hint`

FiniteBaseChange has the only retained hint probe: `Site .ordinary X ≟ X.ProEt`. It typechecks with Kernel checking skipped, but no fixed-expression Kernel improvement is claimed because the mismatch is entered after elaboration. OrderedSpectral, EtaleHom, and F66Adj have no safe hint that isolates a genuine metavariable assignment while preserving the imported theorem/provider and root obligation; mechanical tautological hints were discarded.

## Limits

The READY2 patch exposes root comparison/WHNF partitions and inclusive path samples. It does not expose exclusive time for an individual `NatTrans.app`, `DFunLike.coe`, `Functor.obj`, or `Matrix.charmatrix` branch, local-context fingerprints, or cache hit/miss state. Therefore operation names in the table are path attribution, while H1/H2/H3 classifications are limited to the measured whole-bundle controls.

## IM round 2: diagnostic matched controls

Fresh measurements use Lean/READY2-4.35.0 and current-case source head `03f2a41973c` (master `f21ef672d31` oleans plus targeted Stability rebuilds). Every M below has one provider on both sides, syntactically different elaborated operands, an `exact h` consumer, and a recursive READY2 root. M is **diagnostic** in every case: it keeps the named operation family and data-bearing type but replaces O's larger dependent proposition or final endpoint obligation. Thus a cheap M cannot alone prove H2 for the original root. Times are counters-mode root times, not whole-process wall times.

| Case | Diagnostic M construction | M root | Fresh O root | §1.3 verdict |
|---|---|---:|---:|---|
| F66Adj | same derived counit `.app`, beta-expanded object | 5.933 ms / 881 calls | 29,648.574 ms / 3,897,905 | H2 support from O/A/R; strict M/O inconclusive |
| EtaleHom | same `v.app (op K)` plus same-provider `IsEtaleHomTranspose` control | 2.545 ms / 1,231 calls; proposition 0.066 ms / 10 | 24,301.027 ms / 3,180,470 | H2 support from O/A/R; strict M/O inconclusive |
| ImageHomCounit | same `imageTensorIso.hom.app` and same `Functor.map`, beta-expanded arguments | 4.680 ms / 808 calls; map 0.201 ms / 28 | 48,565.681 ms / 6,359,958 | H2 support from endpoint A/R; strict M/O inconclusive |
| FiniteBaseChange | same triple composite, beta-expanded first `.app` object | 4.627 ms / 640 calls | 612,036.328 ms / 239,340,712 | H2 support from O/A/R; strict M/O inconclusive |
| OrderedSpectral | same coefficient `upperStar.obj`, beta-expanded module | 0.309 ms / 84 calls | 36,145.418 ms / 18,944,709 | H2 support from route A/R; strict M/O inconclusive |
| IntegralComparison | same realization `.app ≫ 𝟙`, beta-expanded `Q.obj` input | 0.729 ms / 54 calls | 73,266.756 ms / 9,426,253 | inconclusive; first-instance A remains expensive |
| RealPurity | same `Matrix.charmatrix` over `PadicAlgCl l`, eta-expanded matrix | 0.029 ms / 15 calls | 53,575.164 ms / 17,310,168 | inconclusive; ring A remains expensive |
| RealPushforward | same `Matrix.charmatrix` over `PadicAlgCl l`, eta-expanded matrix | 0.030 ms / 15 calls | 52,021.014 ms / 17,340,236 | H2 support from polynomial A/R; strict M/O inconclusive |

O versus M branch heads (comparison-exclusive): F66 projection 9,320.076 ms versus 0.337 ms; Etale projection 7,866.536 versus 0.240 ms; Image projection 15,326.563 versus 0.267 ms; Finite failure 519,110.383 ms versus no failure; Ordered failure 32,754.160 ms versus no failure; Integral projection 26,926.832 ms versus a 0.146 ms *total* M comparison; RealPurity failure 46,715.874 ms versus none; RealPushforward failure 45,333.568 ms versus none. These are large call-count and branch-shape changes as well as time changes. The reports give exact calls, comparison/WHNF partitions, depth, Expr/RSS proxies, and the local obligation changed in each M.

The top child pairs are path markers with small direct time. Fresh O trace samples: F66 `DFunLike.coe -> NatTrans.app` has 43,317 ms inclusive at the coercion node (0.085 ms direct); Etale's corresponding coercion child has 45,812 ms inclusive (0.276 ms direct); Image's `Functor.map -> NatTrans.app/Iso.hom` child has 85,614 ms inclusive (0.110 ms direct); Finite's `LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app` child has 778,689 / 778,683 / 778,683 ms inclusive (0.035/0.121/0.378 ms direct); Ordered's `Exists` child has 50,875 ms inclusive, with `Functor.obj` below; Integral's `CategoryStruct.comp -> NatTrans.app` child has 88,003 ms inclusive (0.023/0.185 ms direct); RealPurity and RealPushforward `Matrix.charmatrix` children have 74,003 ms and 71,476 ms inclusive (0.017/0.007 ms direct). Matched children are millisecond or submillisecond scale; Finite's M nested composition nodes have 4.606/4.567 ms inclusive and 0.031/0.041 ms direct. Whole-root branch totals, not these inclusive path times, locate the exclusive cost.

The full restored Finite and RealPushforward replays matter: their earlier `Restored.lean` probes stopped before the root. Fresh restored roots are 625.694 s / 239.341M calls and 53.628 s / 17.340M calls. Etale A/R initially failed while a shared olean was absent, then completed after it reappeared: A has no large root; R is 32.154 s / 3.180M calls. Integral's earlier IM `Original.lean` also stops before the expensive downstream application; the fresh O above uses the actual `DownstreamInstance.lean` site, and a fresh `Restored.lean` replay is 73.107 s / 9.426M calls.

Finite's `unif_hint` now passes full kernel checking. U0 and U1 pretty-printed argument-49 actual/expected propositions match exactly in the audit, including the `ProEt`/`Site` divergence; U1 has the same 239,340,712 calls and branch counts as U0, with root time 632.768 s versus 612.036 s. The hint did not change the elaborated pair or kernel comparison problem. The U0/U1 audit elaboration wall times were 4.59/4.58 s; no separate unification-attempt counter is available. No other case has an applicable hint that changes an open implicit/provider choice without replacing the stored theorem's obligation.

The result is narrower than the Round 1 table: a nontrivial, same-provider operation comparison can be cheap, while the original dependent context can be extremely expensive. These diagnostic M controls do not establish that every matched full-root obligation is cheap. H1 for the exact original dependent roots remains open in all eight cases; RealPurity and IntegralComparison especially do not support a simple H2 verdict because their A controls remain expensive.
