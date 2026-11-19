# IntegralComparisonPullbackRealizationShifts: nested representation audit

Source: `b400b43ec29`, `SmoothPurity/Integral/Comparison/IntegralComparisonPullbackRealizationShifts`,
`integralComparisonPullbackRealization_commShift`; Lean/Mathlib 4.35.0,
200,000 heartbeats. Measurements are reused from
`WORKPLAN-EXPERIMENTS.md`; unchanged fixture links are in `probes/nd/`.
Kernel-only time/heartbeats and separate synthesis time are unavailable.

## Original context and A records

The cost site is the explicit `change` after `commShift_of_localization`
and `intro P m`, before later square normalization. The goal and proposed
target are `Eq` propositions over category morphism compositions and
`NatTrans.app`. Under `Quiver.Hom` / `Functor.obj` / `DerivedCategory`, the
first stored instance difference is `integralTowerHasDerivedCategory` in
the actual goal versus `integralOperationsCommHasDerivedCategory` in the
target. Both are regular height-28 paths to `HasDerivedCategory.standard`.
Section-10 fields shared by the rows: instance depth and field count are
the original unvaried integral tower; the equality uses its morphism type
and both composite sides. Source elaboration reruns in each variant.
Explicit instance terms, synthesis time, Kernel-only time/heartbeats, and
same-term Kernel replay are unavailable. Prior diagnostics at this `change`
counted 1,047,896 `PresheafOfModules.obj` unfolds downstream; that count
does not identify the first costly child.

| Record | Changed factor | First remaining difference | Kernel result | Wall s | CPU user+sys s | RSS KB | Same site/obligation | Confidence |
|---|---|---|---|---:|---:|---:|---|---|
| A-IC-0 | original `change` pair | `HasDerivedCategory` instance | ok, expensive | 83.65 | 85.45+0.99 | 8,531,840 | yes | confirmed site |
| A-IC-I | replace only target's corresponding instance applications | `ObjectProperty.FullSubcategory`/`CochainComplex` under `Functor.obj` | ok, expensive | 83.15 | 84.86+0.98 | 8,540,916 | yes | confirmed negative leaf-alignment control |
| A-IC-K | same aligned target, skip Kernel | same pair | diagnostic only | 4.20 | 4.62+0.78 | 2,984,412 | yes but Kernel disabled | phase control only |

The first two normally Kernel check the same `change` obligation and
`AlignInstance` verifies the intended elaborated expression change.
`AlignInstanceSkipKernel` is never counted as a successful Kernel result;
its timing supports that the remaining cost is Kernel-side. A prior local
instance declaration changed neither stored pair nor cost. The checked
`After.lean` proof changes more than this one instance path and is only a
within-case fast control, not a one-factor A variant. No four-quadrant
provider matrix or explicit-instance replay was obtained.

## D: representation provenance

| Role | Actual goal | Proposed `change` target |
|---|---|---|
| Original declaration | localized `commShift_of_localization` goal | local explicit target in historical proof |
| Data | realization and good-localization endpoint, `NatTrans.app` composite | `DerivedCategory.Q.obj P.obj`, pullback/reduction composites |
| Instance path | `integralTowerHasDerivedCategory` | `integralOperationsCommHasDerivedCategory` |
| Construction | integral tower localization wrapper | operations-comm specialization |
| Proof abstraction | no first-divergence evidence | no first-divergence evidence |

First divergence is the stored instance argument in a derived-category
object; after its direct alignment the first difference moves to a
functor-object argument and the expensive conversion persists. This
identifies the two producers but weakens any claim that the first instance
leaf is sufficient. D confidence: confirmed for provenance and negative
leaf test; dominant downstream difference unresolved.

**Evidence level:** below section-12 Level 1 for the proposed instance
cause. The exact-site negative control is informative, but no positive
single-factor A result or B/C amplification is available. No Level 2/3.
