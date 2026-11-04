# Report 4 — Is opacity needed? The transparent canonical-API control (A1)

Follows `DiagnoseGuide4.md`. **Result: opacity is not needed.** Report 3's working canonical-API
variant, with only its `attribute [irreducible]` line removed (A1), compiles cleanly under
ordinary kernel checking. Across three interleaved runs it is indistinguishable from the
`[irreducible]` control (A3). The same holds for an ordinary imported API module (A2) against the
`@[no_expose]` module (A4). The speedup of Report 3 comes from **vocabulary consistency (H1)**, not
from hiding the wrapper. Preserving the original statements still needs the Report 2 boundary
(H5).

New artifact: `WeilConjectures/ReproducerTransparentFixed.lean` (Track A). Fallback for Track P,
unchanged: `WeilConjectures/ReproducerFixed.lean` (Report 2).

## Environment

| item | value |
|---|---|
| Lean / Mathlib | 4.33.1 (819816b2e0a3) / v4.33.1 |
| worktree | `slopmaster2` @ `55376e1a604f504c0e4a670a051e87c9ac9acb5b`; only untracked report and reproducer files |
| options | `-DElab.async=false -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dbackward.isDefEq.respectTransparency=false -DmaxSynthPendingDepth=3 -Dwarn.sorry=false -Dlinter.style.longLine=false`, default `debug.skipKernelTC=false`, default heartbeats |
| machine | 24 cores / 94 GB, shared; load average **37–96** during this round, so wall times are noisy |
| workspace | session scratchpad `guide4/` (sources, logs, `run.sh`), API module in `guide4/nx/ScratchG4/`; Report 3 sources reused verbatim from `wrap/` and `nx/ScratchNX/` |

## Variants

Report 3's sources were reused as is. A1 is `wrap/v_irr.lean` minus exactly one line
(`diff`: `86d85 < attribute [irreducible] moduleObjectDerivedPullback`), with no other
transparency attributes present (checked by grep).

| variant | track | wrapper | layout | proof | result | elab / kernel (profiled) |
|---|---|---|---|---|---|---|
| **A1** transparent canonical | A | ordinary `def` | single file | original `exact h2` / `congr 1` | **0 errors** | 2.97 s / 3.02 s (only declaration > 0.3 s: 0.45 s) |
| **A2** transparent imported | A | ordinary `def` in an imported module (`ScratchG4.TransparentAPI`: def, `rfl` equality lemma, `…Comp/Id`, assoc/unit lemmas) | API module + consumer; consumer part identical to A1 (`diff`) | same | **0 errors** | consumer 1.07 s / 0.44 s; API module once: 3.6 s / 2.96 s |
| A3 `[irreducible]` (diagnostic, Report 3 `v_irr`) | A | `def` + local `[irreducible]` | single file | same | 0 errors | – |
| A4 `@[no_expose]` (diagnostic, Report 3 `v_nx`) | A | `@[no_expose]` in an imported module | API module + consumer | same | 0 errors | – |
| P0 checked fallback (`ReproducerFixed.lean`) | P | ordinary `def` | single file | Report 2 component lemmas + `Eq.trans` | 0 errors | (Report 2: ~3 s kernel per repro theorem) |
| M0 original mixed | – | ordinary `def` | single file | original | elab + kernel timeouts (Reports 1–3; not rerun, per stop condition) | – |

### Repeated, interleaved timings (profiler off; A1 → A3 → A2 → A4 per round)

| round | A1 transparent | A3 irreducible | A2 imported transparent | A4 imported no_expose |
|---|---|---|---|---|
| 1 | 31.7 s / 26.1 s / 1.99 GB | 30.0 / 25.3 / 1.99 | 12.5 / 8.2 / 1.98 | 10.1 / 6.9 / 1.98 |
| 2 | 31.0 / 25.2 / 1.99 | 35.4 / 28.4 / 1.98 | 12.9 / 8.3 / 1.97 | 12.4 / 7.5 / 1.97 |
| 3 | 32.7 / 27.4 / 1.98 | 29.3 / 26.3 / 1.99 | 7.9 / 5.8 / 1.98 | 8.7 / 6.6 / 1.98 |

(wall / user CPU / peak RSS.) One-time API module compilation: A2 27.6 s wall / 24.0 s user /
2.08 GB; A4 23.5 / 19.6 / 2.09 (Report 3). P0 in the same session: 39.9 / 36.5 / 2.09 GB (three
theorems with the Report 2 helpers; not an apples-to-apples comparison with A1). The final
artifact `ReproducerTransparentFixed.lean`: 27.7 / 25.0 / 1.99 GB.

A1 vs A3 and A2 vs A4 differ by less than the run-to-run noise. Kernel time is about 3 s for the
whole single-file variant and under 0.5 s for the imported consumer.

## A1 contract

1. `moduleObjectDerivedPullbackComp Λ f g : moduleObjectDerivedPullback Λ (f ≫ g) ≅
   moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f`;
   `moduleObjectDerivedPullbackId Λ X : moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 (DerivedCategory …)`
   (`#check`).
2. The assoc and unit lemmas have the intended wrapper-vocabulary types and are proved by the
   upstream `leftDerivedUpperStarComp_*_app` terms. Each is cheap: no declaration besides one at
   0.45 s exceeds the 0.3 s profiler threshold.
3. `dncPullbackComp_congr_left/right` check cheaply, below the threshold.
4. **The consumer statements changed vocabulary** (`leftDerivedUpperStarComp/Id` →
   `moduleObjectDerivedPullbackComp/Id`), checked by `diff` against `Reproducer.lean`. A1 is
   Track A, not Track P.
5. The proof scripts are unchanged (`exact h2`, `congr 1`) and pass the ordinary kernel. Axioms of
   `repro_exact_elab_timeout`, `repro_congr_kernel_timeout`, `dncPullbackComp_congr_left` and
   `moduleObjectDerivedPullbackComp_assoc_app`: `[propext, Classical.choice, Quot.sound]`.

## Causal interpretation

| hypothesis | verdict | evidence |
|---|---|---|
| H1: vocabulary consistency is sufficient | **supported** | A1 passes with an ordinary `def`; same cost as A3 |
| H2: elaborator transparency still matters | **not supported** | A1 vs A3: elaboration 2.97 s vs ~2.8 s (Report 3), total CPU overlaps |
| H3: kernel conversion remains costly with a transparent def | **not supported** | A1 kernel 3.0 s for the whole file; no declaration over 0.45 s |
| H4: module placement or imports confound | **not supported** | A2 (transparent, imported) ≈ A4 (no_expose, imported); A1 ≈ A3 in-file; the in-file/imported gap is just where the API is compiled |
| H5: keeping the original statements needs a different boundary | **supported (existing evidence)** | the original mixed statements fail with every wrapper setting (Report 3 M0/`v_abbrev`/`v_red`/`v_imp_plain`). Converting a canonical-vocabulary result back to the original statements times out (Report 1 X7a/X7b). Only the Report 2 Y4 boundary works. Not rerun here, per the guide's stop condition on known deterministic timeouts |

Separate contributions:
* **Vocabulary alignment** is what removes the costly conversion. With compositors typed in the
  same spelling as the functors, `h2`'s type matches the goal except for proofs, so no
  cross-spelling composite is ever compared under `NatTrans.app`/`Functor.map`.
* **The regular-definition head** (`moduleObjectDerivedPullback` as a `def`) is kept and helps.
  Removing it breaks statement elaboration (Report 3 `v_nowrap`).
* **Elaborator reducibility** (`[irreducible]`) and **module visibility** (`@[no_expose]`) make no
  measurable difference once the vocabulary is aligned. Their only real effect, seen in Report 3,
  is to turn mixed-vocabulary statements into type errors (a linting-like guard), not to speed
  anything up.
* The underlying kernel reduction path behind the original slowdown remains an untraced
  hypothesis (projection heads with `abbrev` hints unfolding into the derived-category machinery).

## Final candidates and compatibility

* **Track P (original statements, drop-in):** `ReproducerFixed.lean` (Report 2), unchanged and
  re-verified this round: 0 errors, statements byte-identical to `Reproducer.lean`, standard
  axioms. Still the only option that keeps the theorem types.
* **Track A (canonical transparent API):** `ReproducerTransparentFixed.lean`. No `opaque`,
  `@[no_expose]` or `[irreducible]`. Same code as A1 apart from comments and line wrapping
  (checked by comment-stripped `diff`). Its "Upstream part" comment lists the additions needed in
  `CondensedModuleDerivedPushpull.lean`: `…Comp/Id` typed in the wrapper vocabulary, their
  assoc/unit lemmas, and an optional `moduleObjectDerivedPullback_eq := rfl`. Nothing existing
  changes and nothing becomes opaque, so the 61 existing users of the wrapper (including those
  that `unfold`/`delta` it) keep compiling. This is unlike the opaque variant, where they would
  break. Migrating consumers to the canonical vocabulary is optional, file by file.
* Downstream: the A2 consumer is a real importer of a transparent API module and works. No shared
  repository file was modified, so no repository consumer needs a rebuild. A migration of real
  upstream files was not attempted (constraint 7).
* `ReproducerOpaqueFixed.lean` (Report 3) is superseded by the transparent file and should not be
  used.

## Next-step recommendation

(b) for new or refactored code, adopt the **transparent canonical API** in an explicitly approved
scope: add `moduleObjectDerivedPullbackComp/Id` and their coherence lemmas upstream, and state new
coherence results in that vocabulary. (a) Keep the Report 2 Y4 proof wherever the original
`leftDerivedUpperStarComp/Id` statements must stay. Before any wider adoption, the smallest useful
next experiment is to move the five API declarations into `CondensedModuleDerivedPushpull.lean`
and rebuild one real consumer that currently mixes vocabularies, to measure the end-to-end effect.
