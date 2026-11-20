# STRUCTURE EXPOSURE AUDIT

Case: `IntegralComparisonPullbackRealizationShifts`
Source snapshot: `b400b43ec29`, `integralComparisonPullbackRealization_commShift`
Lean/Mathlib: 4.35.0, one Lean thread, normal Kernel checking, 200,000 heartbeats

## R1. Exact Kernel cost site and initial mismatch

The first expensive operation is the explicit `change` after
`commShift_of_localization` and `intro P m`. The pre-change goal is an equality
at `(integralOperationsGoodLocalization ...).obj P`; the changed goal spells
the endpoint as `DerivedCategory.Q.obj P.obj` with
`integralDerivedPullback`, `SY.reduction ⋙ H`, and explicit shifts. Under the
common `Eq`/`Quiver.Hom`/`Functor.obj` path, the first visible mismatch is
`integralTowerHasDerivedCategory` versus
`integralOperationsCommHasDerivedCategory`, repeated on both equality sides.
The post-change prefix costs 86.06 s (full Before 105.67 s); the pre-change
prefix is 7.90 s.

## R2. Candidate exposure boundary

The boundary is the `Functor.obj` argument to `DerivedCategory`, specifically
the stored `HasDerivedCategory` instance. Both heads are regular definitions
of equal height, so hint metadata does not choose an order. One-step bodies
lead to `HasDerivedCategory.standard`; this is a source-level prediction, not
an internal trace.

## R3. Exposed data-bearing structure

```text
localization comm-shift equation
|- good-localization object versus DerivedCategory.Q.obj endpoint
|  |- HasDerivedCategory instance path
|  |- Functor.obj and derived pullback functors
|  |- PresheafOfModules.obj and module/additive instances
|  `- explicit shift functors and natural-transformation apps
|- CategoryStruct.comp / Quiver.Hom endpoints on both sides
`- later Add.add and reduction data
```

Diagnostics at this exact conversion report 1,193,814 `Add.add`, 1,047,896
`PresheafOfModules.obj`, and 812,294 `AddMonoid.toAdd` unfolds. These are
downstream footprint measurements, not a causal trace of the first leaf.

## R4. Cost distribution and reduction footprint

The `change` conversion accounts for most of the full cost. Aligning only the
stored instance argument (`C3-I`) changes the first visible difference to a
`FullSubcategory` versus `CochainComplex` object under `Functor.obj` and still
takes 83.15 s. Kernel-skipping that same aligned probe takes 4.20 s, confirming
the remaining cost is Kernel-bound. The complete historical After is 23.61 s,
but changes wrapper/interface vocabulary beyond this one factor.

## R5. Causal control

`C3-I` uses a definitionally equal `change` target and verifies the elaborated
pair changed at the selected instance path, while retaining the same goal and
consumer. It is a negative control: time and memory remain unchanged. A valid
one-factor child alignment was prevented by the dependent endpoint bundle; the
full After is the available whole-bundle control.

## R6. Exposure-footprint comparison

Original: endpoint conversion exposes the concrete presheaf/module/functor
bundle and the large unfold counters.
Instance-aligned: the first leaf moves, but the deeper object representation
and essentially the same footprint remain.
Restored: the original target pair and cost return in `Before.lean`. No
successful §6 restoration alignment is claimed because the one-factor control
was negative.

## R7. Classification and confidence

Classification: **U**, with a **P4 candidate** (intrinsic reduction remains
after the first visible instance alignment).
Confidence: **Confirmed** for the `change` cost site and the negative
instance-leaf control; **Plausible** for the deeper object mechanism.
Directly measured: pre/post timings, changed pair, counters, and skip-Kernel
phase control. Structurally inferred: the nested endpoint tree. Unknown: the
first causal child under `Functor.obj`.

## Most important result

The first instance mismatch is not sufficient. A deeper presheaf/module/functor
representation remains expensive after that leaf is aligned, so this case must
remain separate from the confirmed bundle controls.
