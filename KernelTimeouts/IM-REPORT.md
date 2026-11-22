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
