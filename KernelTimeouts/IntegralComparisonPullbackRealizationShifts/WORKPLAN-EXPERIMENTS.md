# IntegralComparisonPullbackRealizationShifts workplan experiments

Source snapshot: `integralComparisonPullbackRealization_commShift`,
module `SmoothPurity/Integral/Comparison/IntegralComparisonPullbackRealizationShifts`,
commit `b400b43ec29`; Lean and Mathlib 4.35.0. The costly site
is the explicit `change` after `commShift_of_localization` and
`intro P m`. `probes/HeadAudit.lean` preserves the original goal,
local context, and target before comparison. Both propositions are
`Eq` over category-morphism composites. The first structural
divergence is in `Eq`'s `Quiver.Hom` type, under
`Functor.obj` and `DerivedCategory` argument 4:
`integralTowerHasDerivedCategory` in the actual goal versus
`integralOperationsCommHasDerivedCategory` in the proposed
target. The same difference recurs in the equality sides.
Both are regular definitions of height 28 whose immediate bodies
lead to `HasDerivedCategory.standard`.

All timed probes used one Lean thread, `timeout 3600`,
`/usr/bin/time -v`, and fixed process concurrency of one.
The source heartbeat limit is 200,000. Kernel-only time and
heartbeat consumption are not separately available. The
diagnostic probes end with `sorry` after the `change` site;
they measure that site, not a completed theorem.

## C3-I: Align the stored instance argument

EXPERIMENT: C3-I; group: G1-B/G3-B. Hypothesis: the distinct
`HasDerivedCategory` instance leaf is sufficient to cause
the long goal conversion. BASELINE: `probes/HeadAudit.lean`
compares the exact unaligned pair at the original `change`
site. It takes 83.65 s wall, 85.45 + 0.99 s CPU,
8,531,840 KB RSS. CONTROL: `probes/wp/AlignInstance.lean`
elaborates the same explicit target and replaces only
corresponding `integralOperationsCommHasDerivedCategory`
instance applications with the actual goal's
`integralTowerHasDerivedCategory` applications. All other
target subterms are preserved. The Lean-level `change`
accepts this definitionally equal target, so the theorem
obligation and local context are preserved. Normal Kernel
checking is enabled.

The probe prints both expression pairs. Before alignment, the
first difference is the two instance constants above. After
alignment, the first divergence moves to a nested
`Functor.obj` argument:
`ObjectProperty.FullSubcategory` versus `CochainComplex`.
Thus the source edit changes the elaborated pair at precisely
the selected instance path, while the same `change` conversion
remains. RESULT: 83.15 s wall, 84.86 + 0.98 s CPU,
8,540,916 KB RSS. The time and memory are indistinguishable
at this scale from the baseline. Supports: a downstream
representation mismatch survives the instance alignment.
Weakens: the first instance leaf alone is causal for the
85-second cost. Unresolved: which deeper functor/object
argument dominates. Classification: unfavorable nested
representation path, with the instance leaf as a first
visible difference. Confidence: confirmed negative result
for instance alignment; plausible deeper mechanism.

## C3-K: Phase control for the edited target

EXPERIMENT: C3-K; group: phase diagnostic. Hypothesis:
C3-I's remaining 83 seconds are still Kernel-bound rather
than a new elaboration cost from the custom `change` tactic.
BASELINE: C3-I above, with normal Kernel checking.
CONTROL: `probes/wp/AlignInstanceSkipKernel.lean` differs
only by `debug.skipKernelTC true`. The same aligned
expression pair is constructed and printed, but Kernel
checking is intentionally skipped. The mathematical
obligation is the same; this control is not counted as
a successful proof. RESULT: 4.20 s wall,
4.62 + 0.78 s CPU, 2,984,412 KB RSS. Supports: the
remaining cost in C3-I is Kernel-bound. Weakens: a new
Meta-level `change` cost explains the flat timing.
Classification: diagnostic only; confidence: strongly
supported.

## Earlier negative source control

`probes/LocalTowerInstance.lean` added a local tower
instance but left the first divergent elaborated pair
unchanged and remained expensive. Its result is not
interpreted as an instance-alignment experiment. The new
C3-I control changes the stored instance argument itself.

## Mechanism

The first unequal argument under the shared
`DerivedCategory` head is a concrete instance. Replacing
that argument with the actual goal's instance is accepted,
but uncovers a different concrete functor-object
representation and does not reduce Kernel cost. The
instance mismatch is therefore not a sufficient explanation
of the original long conversion. The next causal
subexpression under `Functor.obj` remains to be isolated;
no claim is made about equal-height Kernel unfold order.
