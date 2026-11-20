# DefEq Internal Cost Experiments

Case: `IntegralComparisonPullbackRealizationShifts`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: `change` conversion after `commShift_of_localization` and `intro P m`.
Instrumentation: observational counters/trace build; round-two downstream diagnostics.

## A1: Original endpoint conversion

Baseline root: `original.lean`/`prefix-control.lean` exact site. Counters measured 110.020 s root wall, 9,426,253 recursive calls, maximum depth 183, 68.656 s comparison-exclusive and 41.363 s WHNF-exclusive. The trace sample had 1,781,432 exact repeats and 0.712 s sampled repeated immediate exclusive time. The profile is mixed but comparison-leading and deep; `PresheafOfModules.obj`, `Add.add`, `AddMonoid.toAdd`, `CategoryStruct.comp`, and `Functor.obj` are frequent heads, not individually causal timings.

## A2: First instance-path alignment

Control: `instance-control.lean`, a type-correct `change` with the first `HasDerivedCategory` instance path aligned. The first raw difference moves, but the downstream `FullSubcategory`/`CochainComplex` and presheaf/module bundle remains. The matched diagnostic took 83.15 s and the downstream round-two diagnostic took 88.99 s wall (90.65 s user, 1.21 s system, 8,314,760 KB RSS). The original consumer and endpoint obligation are retained, but the control is negative: the root remains expensive.

## C validity

A strict C comparison of isolated arguments is invalid here. Replacing the endpoint bundle changes the dependent `change` target and no longer checks the original obligation. The full historical `After` source is a whole-bundle representation change, not an isolated dependent-domain control. No C cost is claimed.

## Conclusion

The first instance leaf is not causal by itself. Aligning it leaves nearly the same deep presheaf/module/functor comparison. The actual dominant downstream pair remains unresolved by the available instrumentation; the large counters are measured footprint, not field attribution.

## READY2 round 2

The READY2-4.35.0 `DownstreamInstance` probe reached the actual downstream root in 73.839 s with 9,426,253 calls, 44.816 s comparison-exclusive time, and 29.024 s reduction-exclusive time. Dependent comparison/reduction contributed 40.189 s / 26.654 s; the proposition timer was 268.261 s and is overlapping. The Expr proxy created 438,986,428 expressions / 14,632,433,896 bytes, with a 5,418,057,728-byte RSS/commit delta.

The detailed trace root was 88.313 s (19.6% overhead). Its top path was the nested `CategoryStruct.comp` -> repeated `NatTrans.app` chain under `root/argument[2]/argument[7]`; one repeated `NatTrans.app` descendant accounted for 46,686 ms and the enclosing chain 88,312 ms. The prefix/first-instance probes remained small or negative controls. This locates the cost in the downstream dependent endpoint rather than the first visible instance leaf.

The READY2 rerun of the first-instance control did not elaborate: the probe imports `HeadAuditTools`, which is not present in the built search path. It exited before a Kernel root was entered, so the earlier 83--89 s first-instance measurements remain the only valid control numbers and no READY2 allocation/path number is claimed for that control.
