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
## Round 2 and v2 addendum

DownstreamInstance completed in 88.99 s wall (90.65 s user, 8.31 GB peak RSS) at the original change site. Same-site diagnostics include 1,193,814 Add.add, 1,047,896 PresheafOfModules.obj, 812,294 AddMonoid.toAdd, and 333,085 Functor.obj kernel unfolds. First-instance alignment remains negative; the first materially changed downstream region is the presheaf/module object bundle.

### STRUCTURE EXPOSURE AND AMPLIFICATION ADDENDUM

**A. MISMATCH SEMANTICS.** The two HasDerivedCategory paths are syntactically different, but first-leaf alignment only moves the first visible difference. It is not a causal trigger for the parent cost. The unresolved candidate is deeper under Functor.obj; classification remains U.

**B. EXPOSURE.** The boundary is the endpoint Functor.obj used by change. The tree contains derived-category instances, pullback/reduction functors, PresheafOfModules.obj, additive/module instances, shifts, and natural transformations. Large presheaf/module counters are measured at the downstream conversion; the first leaf is only comparison-relevant.

**C. COST MECHANISM.** The downstream site is reduction-heavy and repeated across endpoint compositions. Instance alignment leaves the 88.99 s run and large footprint. Counters are inclusive.

**D. FIXED-TRIGGER ABLATION.** Invalid: the candidate trigger is not isolated, and the dependent endpoint cannot be parameterized without changing the change obligation. No fixed-trigger claim is made.

**E. REDUCTION-PATH AUDIT.** Both sides share Functor.obj; aligning the stored instance moves the first difference to FullSubcategory versus CochainComplex under that head. This is measured path movement, not an internal trace.

**F. MISMATCH PROVENANCE.** Distinct generic/local HasDerivedCategory providers are selected during elaboration. Consumption by change and then presheaf/module and shift functors makes the deeper representation relevant.

**G. CONCLUSION.** U with a P4 candidate, evidence level 1. Negative first-leaf control and downstream counters are strongest; unchanged time is contrary to first-leaf causality. A typed whole-endpoint control aligning the PresheafOfModules provider is the next falsifier.
