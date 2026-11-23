# CCMOA: Slow Derived Tensor

Case: KernelTimeouts/Historical/SlowDerivedTensor

## Scope and provenance

This is the P7 Kernel negative control. I reused the existing MOE S0-S6
record, the round-two A0/A2 probes, and the READY4.2 counter run. The
baseline source is bdab171985a; the control source is 428569e1ce1.
No new long replay was needed. Raw values are in ccmoa/slow-snapshot.txt.

## Experiment A: stage audit

| Stage | Snapshot |
| --- | --- |
| S0 | The consumer is isLeftDerivedFunctor2_derivedTensor; the baseline helper predicates are abbrev, while the control changes the same bodies to @[reducible] def. |
| S1 | No relevant macro boundary was found. The imported MOE syntax record is source-required; the recursive syntax dump was not retained. |
| S2 | Round-two A0 and A2 have the same recorded tensorObj outer sizes (2279/15735), heads, and instantiated provider sizes (1785/11973). This is the negative-control Meta-level shape; no claim of structural equality is made. |
| S3 | Pre-finalization data for the imported consumer is unavailable. |
| S4 | The stored type/value trees preserve the full pair. The first recorded structural difference is the hash pair at root/body/body/body/body/body/body/body/body/body/body/body/body/arg/fn/fn/fn/fn, 684061942 versus 3524748218. Stored tensorObj is abbrev; DerivedMonoidal is regular:2. The control changes HasLeftDerivedFunctor2 and IsLeftDerivedFunctor2 from abbrev to regular reducible definitions. |
| S5 | The root replay returns true. At M0 the pair is tensorObj versus tensorObj; its second argument is inferInstance versus inferInstance, with provider sizes 1785/11973. |
| S6 | Kernel reduction exposes the dependent HasLeftDerivedFunctor2 proposition below the provider. The READY4.2 baseline root has 6269622 calls, 23642.214 ms comparison-exclusive time, and 19981.705 ms reduction-exclusive time. The dominant downstream positions are dependent Functor.obj, CategoryStruct.comp, DFunLike.coe, and proof propositions. |

The earliest exact structural divergence is therefore supported at S4/S5.
The source declaration-kind choice is visible at S0, while the saved S2
negative-control shape is unchanged. The divergence is active at the M0
conversion, not merely a pretty-printer difference.

## Experiment B: one-factor control

The valid control is the declaration-kind change from abbrev to
@[reducible] def for the derived-functor helper predicates. It retains the
consumer statement and the recorded tensor/provider Expr shape. A0 and A2
both check successfully and both retain the 46-52 second tensor-argument
conversion:

| Variant | Expr change | Full consumer conversion | Counter data |
| --- | --- | ---: | --- |
| A0 baseline | HasLeftDerivedFunctor2 and IsLeftDerivedFunctor2 hints are abbrev; tensor/provider sizes 2279/15735 and 1785/11973 | 119953/127832 ms forward/reverse | READY4.2 root 613: 6269622 calls; 23642.214/19981.705 ms comparison/reduction |
| A2 control | same recorded tensor/provider shape; those two helper hints are regular reducible definitions | 2/2 ms forward/reverse | no separate A2 counter file; round-two output records the same tensor shape and 1 ms value check |

The tensor argument itself does not get cheaper. The consumer boundary does.
Because the control changes declaration metadata in several related helper
definitions and lacks a second counter dump, this is strong negative-control
evidence for Kernel hint/strategy involvement, not a strict same-Expr F2
causal replay. The source spelling is restored by A0 and the expensive
consumer conversion returns.

## Experiments C and D

C: Not observed. The saved S2 shape does not identify a changed instance
assignment, coercion, or transparency decision.

D: Unknown. The imported consumer has no pre-finalization term. The S4
record is explicitly observational at the environment boundary.

## Experiment E: boundary inventory

| Boundary | Current behavior | Puncture | Status |
| --- | --- | --- | --- |
| HasLeftDerivedFunctor2 / IsLeftDerivedFunctor2 declaration head | A regular reducible head lets the consumer conversion finish in 2/2 ms while the tensor argument remains expensive; the baseline abbrev path exposes the dependent body. | Restore the original abbrev declarations. The full consumer returns to 119953/127832 ms. | Fragile but effective |
| tensorObj argument 2 | Same-head tensorObj conversion descends into provider bodies of sizes 1785/11973 and remains 46-52 seconds in both A0 and A2. | Changing the helper declaration kind does not puncture this tensor argument. | Not actually responsible for the A2 speedup |
| Imported declaration finalization | Stored hints and trees are observable; pre-finalization consumer data is absent. | No valid puncture available. | Untested |

## Synthesis

| Case | Earliest divergence | Primary origin | Elaborator causal? | Finalization causal? | Kernel-exposed latent difference? | Effective boundary | Boundary fragility |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Slow Derived Tensor | S4/S5 | source declaration metadata plus Kernel strategy | Not observed | Unknown | Strongly supported | regular helper-definition head | Fragile but effective |

Evidence is deliberately bounded: the exact S4/S5 pair and the restored
consumer workload are demonstrated, but the missing A2 counter dump and
unavailable pre-finalization term prevent a Demonstrated metadata-only F2
claim.
