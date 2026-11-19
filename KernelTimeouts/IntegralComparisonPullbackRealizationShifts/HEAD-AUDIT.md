# IntegralComparisonPullbackRealizationShifts head audit

## Case and conversion

- Case ID: `IntegralComparisonPullbackRealizationShifts`; conversion ID: `IC-change-v1`.
- Declaration: `integralComparisonPullbackRealization_commShift`, from `b400b43ec29`; module `SmoothPurity/Integral/Comparison/IntegralComparisonPullbackRealizationShifts`.
- Lean/Mathlib: 4.35.0; baseline `Before.lean` at dataset revision `7118b5fe0097`.
- Site: explicit `change` after `commShift_of_localization` and `intro P m`. The original elaborated goal is saved by `probes/HeadAudit.lean` before evaluating `change`, then compared with the new goal before any audit normalization. Local context includes the pullback functors `A`, `D`, `L`, `B`, `H`, `J`, `T`, the comparison `ψ`, realization `M`, reduction `SY`, and localization proof.
- Actual and expected expressions: equations of category morphism composites. The actual endpoint uses `M.realization` and the good-localization object; the expected endpoint spells out `DerivedCategory.Q.obj P.obj`, `integralDerivedPullback`, and `SY.reduction ⋙ H`.
- Normal Kernel checking enabled. Full Before: 105.67 s wall; Kernel skipped: 11.11 s. Prefix before `change`: 7.90 s. Prefix with `change`: 86.06 s. Heartbeat count for the conversion was not separately measured. CPU/RSS for that original prefix were not retained; the full old source previously reached 9,386,264 KB RSS.

## Head audit

| Side | Raw outer shape | Head metadata | First divergent path |
|---|---|---|---|
| Actual | `Expr.app`, `Eq.{u+3}` with three arguments | `Eq` inductive; no reducibility hint | `Eq` type -> `Quiver.Hom` argument 3 -> `Functor.obj` argument 1 -> `DerivedCategory` argument 4 -> `integralTowerHasDerivedCategory` |
| Expected | same `Eq` head, universe, and arity | same | corresponding leaf is `integralOperationsCommHasDerivedCategory` |

The same divergence recurs in each equality side under `CategoryStruct.comp` -> `Functor.obj` -> `DerivedCategory`. Both instance leaves are regular definitions of height 28, at universes `[u,u]`, with seven applied arguments and a lambda as immediate body shape. Source inspection identifies both as paths to `HasDerivedCategory.standard` for the two presentations of the integral tower modules. The first mismatch is in a **stored instance argument**, not in the visible morphism names. There is no raw projection or recursor on the first divergent path. The current expression also contains concrete functor/object applications and local let values; the audit does not attribute the first mismatch to zeta reduction.

The common outer `Eq` and `Quiver.Hom` heads permit argument comparison. That route reaches distinct regular instance constants with equal heights. The installed hint metadata does not predict which equal-height definition the Kernel will unfold first. One-step expansion exposes a `HasDerivedCategory.standard` instance for each module presentation, after which the dependent `DerivedCategory` and `Functor.obj` arguments must be reconciled. This is a source-guided prediction, not an internal Kernel trace.

## Hypothesis tests

| Hypothesis | Status | Experiment and result |
|---|---|---|
| H1: hint/order | **Tested; not established.** | H1.3 finds two regular height-28 instance heads. There is no abbrev/regular asymmetry or measured same-body hint control. |
| H2: same-head argument | **Tested; supported structurally.** | `HeadAudit.lean` finds the first unequal argument under the common `DerivedCategory` head; its argument 4 is a concrete instance. The `change` prefix costs 86.06 s versus 7.90 s before it, but no one-argument replacement with the identical goal was found. |
| H3: projection | **Not supported at the first divergence.** | Raw-constructor inspection sees applications through `Functor.obj` and `DerivedCategory`, without `Expr.proj` on that path. |
| H4: dependent binder | **Not applicable.** | This site is an explicit goal conversion, not an application-argument domain. Dependent category/object types can amplify the conversion downstream. |
| H5: instance paths | **Observed, causal role plausible.** | H5.1 exposes the two stored `HasDerivedCategory` constants. H5.2 adds a local tower instance in `LocalTowerInstance.lean`; the same `change` still completes in 85.45 s (84.41 + 1.06 s CPU, 8,271,692 KB RSS). `LocalTowerHeadAudit.lean` confirms the original first divergent pair is unchanged. |
| H6: proof irrelevance | **Not supported as the first trigger.** | The first unequal leaf is an instance term used in a data type; no proof body is compared there. |
| H7: non-delta reduction | **Not established.** | The first unequal terms are regular definitions. Later projection, beta, or zeta work is possible but not isolated. |
| H8: context/order | **Not indicated by current controls.** | The isolated post-`change` prefix reproduces most of the full old cost. No same-pair context variation has isolated a cache or check-order effect. |

`After.lean` completes in 23.61 s, but changes the helper interface and wrapper vocabulary beyond this one conversion. It is evidence for a successful full theorem, not a single-factor instance-path control. Diagnostic `sorry` occurs only after the audited `change` in prefix probes; those results are not counted as checked final proofs.

## Causal record

- Initial pair: two `Eq` propositions with shared outer heads and a stored tower-versus-comm `HasDerivedCategory` instance difference inside `DerivedCategory` argument 4.
- Potential cheap route: compare the morphism-domain arguments under the shared `Quiver.Hom` and `DerivedCategory` heads.
- Why it fails syntactically: those instance arguments are distinct regular constants, even though both represent derived-category structure for related module presentations.
- Predicted reduction: expose one or both instance definitions; one-step bodies are lambdas leading to `HasDerivedCategory.standard`. Equal regular heights do not determine the first side from metadata alone.
- Why costly: the differing instance is embedded in concrete derived-category objects and functor applications. Earlier diagnostics at this same conversion reported 1,193,814 `Add.add`, 1,047,896 `PresheafOfModules.obj`, and 812,294 `AddMonoid.toAdd` unfolds. These are downstream counts, not proof of the first Kernel choice.
- Control: adding the local tower instance leaves the first divergent pair and cost essentially unchanged. The full revised proof keeps the localization endpoint vocabulary aligned and completes, but changes several interfaces.
- Verdict: **unresolved** as to whether the stored instance difference alone forces the expensive path. The original `change` necessarily reconciles distinct representations; the measured data do not isolate an unfavorable instance-unfolding choice.

## Evidence and confidence

Observed: preserved pre/post `change` expressions, exact first divergent instance path, regular hints/heights, and the timed local-instance negative control with its unchanged raw pair. Interpretation: H2 is structurally supported and H5 is **plausible** as an amplifier; an instance-aligned same-obligation control remains missing. Overall evidence for the full causal explanation: **plausible**. The expensive conversion site itself is confirmed.
