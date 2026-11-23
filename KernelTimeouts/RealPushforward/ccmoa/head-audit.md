# RealPushforward head audit

## Case and conversion

- Case ID: `RealPushforward`; conversion ID: `RP-final-exact-v1`.
- Declaration: `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one` example, from `ed3d39ddb5d`; module `DeligneLaumon/AffineLine/RealPushforward`.
- Lean/Mathlib: 4.35.0; baseline: `Before.lean` and `probes/FinalExact.lean` at dataset revision `7118b5fe0097`.
- Site: final inferred-type / declared-type comparison at `exact this`, after the two polynomial rewrites. Local context includes `k₀`, `l`, `X`, `Y`, `f`, `K`, `ι`, the point `ξ`, coefficient `n`, and the fiber-expansion witnesses.
- Original elaborated expressions preserved: **yes**, inspected before normalization by `probes/HeadAudit.lean`. Normal Kernel checking is enabled in all timing results below.
- Actual: `Eq ℂ (starRingEnd ℂ (ι ((stalk ... ξ).frobeniusEnd.charpolyRev).coeff n)) (ι (...))`.
- Expected: the same `Eq` shape with `FrobeniusModule.localPolynomial (stalk ... ξ)` in place of `LinearMap.charpolyRev ...`.
- Original `probes/FinalExact.lean`: deterministic Kernel timeout, 54.54 s wall, approximately 4,686,316 KB peak RSS. The type-only and prefix controls take 2.8-3.0 s. The configured heartbeat limit is 200,000; an isolated Kernel heartbeat count was not recorded.

## Head audit

| Side | Outer constructor and spine | Universes | Head metadata | Immediate body |
|---|---|---|---|---|
| Actual | `Expr.app`, `Eq` with type and two equality sides | `Eq.{1}` | inductive | none |
| Expected | `Expr.app`, `Eq` with type and two equality sides | `Eq.{1}` | inductive | none |

The type argument is syntactically the same `Complex`. Each equality side begins with three nested `DFunLike.coe` applications and a `Polynomial.coeff` application. The first unequal polynomial argument is `LinearMap.charpolyRev` (eight arguments, universes `[0, u+1]`, regular definition height 26) versus `FrobeniusModule.localPolynomial` (three arguments, universes `[u+1, 0]`, regular definition height 27). The corresponding outer coefficient, coercion, and equality heads agree. No projection, recursor, or let occurs on the first divergent path; the relevant arguments are data and concrete structure instances, not proof arguments. The result does not depend on reconstructing an application binder domain.

Source inspection shows that one unfolding of `FrobeniusModule.localPolynomial M` exposes `M.frobeniusEnd.charpolyRev`. One unfolding of `LinearMap.charpolyRev f` exposes `f.charpoly.reverse`. The installed 4.35.0 `ReducibilityHints` policy considers the greater regular height first; it therefore predicts unfolding `localPolynomial` before `charpolyRev`. This is a prediction from metadata, not a Kernel trace. The actual stalk and `M.frobeniusEnd` arguments can still require comparison after the polynomial heads align.

## Hypothesis tests

| Hypothesis | Status and experiment | Measurement and interpretation |
|---|---|---|
| H1: hint asymmetry/order | **Tested; not supported as the isolated cause.** H1.3 inspects the one-step body and heights. | The height-27 expected head is predicted to unfold first into the height-26 head, a direct route to alignment. No same-body hint-kind control was available for the imported definitions. |
| H2: same-head argument | **Tested; supported.** `AlignedGoal.lean` replaces only the polynomial representation in the equivalent declared obligation; `AlignedHead.lean` checks the resulting elaborated pair. | Original final conversion: 54.54 s timeout. Aligned full proof: 3.00 s, 2.00 s user + 0.93 s system, 3,128,720 KB RSS, success. The first divergence moves from the polynomial argument of `Polynomial.coeff` to a smaller semiring instance below `Finsupp`. |
| H3: projection | **Not applicable.** | The first divergent path contains ordinary applications, not `Expr.proj`. |
| H4: dependent binder | **Not applicable.** | The hotspot is the final equality-type comparison, after all applications have been formed. |
| H5: instance paths | **Tested; not sufficient alone.** H5.1 compares the exact stored terms in `HeadAudit.lean` and `AlignedHead.lean`. | The fast aligned pair still differs at `Semifield.toCommSemiring` versus `CommRing.toCommSemiring`. This leaf difference alone does not reproduce the timeout. |
| H6: proof irrelevance | **Not applicable at the first divergence.** | The differing polynomial argument is data; no generated proof leaf appears on its first divergent path. |
| H7: non-delta reduction | **Not applicable to the initial trigger.** | Both divergent heads are regular definitions. Later polynomial or stalk computation remains untraced. |
| H8: context/order | **Tested; not supported.** Compare the original declaration and isolated final-conversion probe from `CLASSIFICATION.md`. | Both reproduce the approximately 55 s timeout; the type-only and prefix controls remain near 3 s. No context-sensitive difference was observed. |

The diagnostic `sorry` in the prefix probes discards the final obligation; it is used only to locate the site. `AlignedGoal.lean` is the successful, fully Kernel-checked control.

## Causal record

- Initial pair: equality propositions with the same `Eq`/`Polynomial.coeff` path but different polynomial heads.
- Potential high-level route: `Polynomial.coeff` argument comparison.
- Why that route fails: its polynomial argument is `charpolyRev ...` on one side and `localPolynomial ...` on the other.
- Predicted reduction: unfold the regular height-27 `localPolynomial` side, exposing `frobeniusEnd.charpolyRev` and concrete stalk/module arguments.
- Why expensive: the original comparison must enter that concrete polynomial and dependent coefficient representation; the baseline times out. The exact subsequent Kernel reduction sequence is not observed.
- Control: an equivalent goal using `charpolyRev` on both sides passes in 3.00 s and leaves an instance leaf difference.
- Verdict: **necessary unfolding for the original polynomial representation**. The aligned representation removes that need; the data do not show that the Kernel chose an avoidable first step.

## Evidence and confidence

Observed: the raw heads and first divergence above; the timed original and aligned full proofs; the remaining instance difference in the aligned pair. Interpretation: H2 is **confirmed** as the cause of the expensive initial polynomial comparison. The exact downstream reduction path remains unknown. Overall evidence level: **confirmed** for the representation trigger, **plausible** for any specific downstream instance amplifier.
