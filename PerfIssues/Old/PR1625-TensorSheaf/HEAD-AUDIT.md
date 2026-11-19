# Head audit: PR #1625 tensor-sheaf component

Case ID: `PR1625-TensorSheaf`; conversion ID: `P1625-result-lhs`.
Declaration: `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac`.
Lean 4.35.0, master revision `1ef1fddac73e`. [Before.lean](Before.lean)
restores the original value at its module path with the generated Lake setup;
[After.lean](After.lean) is the well-typed fixed control. Probes use one Lean
thread, synchronous elaboration, ordinary Kernel checking, `nice -n 10`, and
`timeout 3600`.

## Expensive conversion and Head Audit

The target's in-situ Kernel check takes 87.6 s before and 2.43 s after;
whole-prefix user CPU is 188.18/104.15 s, with 8,245,292/2,929,672 KB
peak RSS. [HeadAudit.lean](probes/HeadAudit.lean) rechecks the stored old
value in 335 ms, then compares its inferred and declared types in 95.520 s.
Thus the expensive step is the *final type conversion*, not checking the
28-argument `Functor.leftDerived₂NatTrans_app_app` application. The latter's
last four argument-domain comparisons take 0, 338, 0, and 0 ms
([ApplicationPrefixes.lean](probes/ApplicationPrefixes.lean)).

After opening 15 original binders, the exact pair is `Kernel.check` of the
stored body versus the declared theorem result with the same free variables
substituted. Both sides are `Expr.app`, headed by the same `Eq` constant.
The carrier is `Quiver.Hom`; both equality sides are `CategoryStruct.comp`.
The carrier comparison takes 2 ms, left-hand composition 93.679 s, and
right-hand composition 904 ms ([ResultArguments.lean](probes/ResultArguments.lean)).
At the left composition, both `CategoryStruct.comp` heads are the same
`abbrev`, with seven arguments; arguments 0-4 and 6 take at most 1 ms each.
Argument 5 is a `NatTrans.app` pair costing 96.236 s
([ResultLhsArguments.lean](probes/ResultLhsArguments.lean)).

The two `NatTrans.app` expressions each have eight arguments and the same
head. Arguments 0-5 and 7 compare in 0-2 ms; argument 6 is another
`NatTrans.app` pair and takes 95.717 s. Both `CategoryStruct.comp` and
`NatTrans.app` are `abbrev` definitions whose immediate post-lambda bodies
are `Expr.proj CategoryStruct.2` and `Expr.proj NatTrans.0`, respectively.
[NatTransMajor.lean](probes/NatTransMajor.lean) replaces only the right
outer `NatTrans.app` major premise (argument 6) by the definitionally equal
left one. The replacement Kernel-checks and its result type is structurally
identical to the original right expression's type. The original pair takes
95.869 s, the aligned pair 0 ms, and right-original versus right-aligned
93.567 s. This isolates the differing concrete major-premise expression as
the costly dependency; the first divergence within its nested `NatTrans.app`
has not been isolated.

## Source-guided prediction and hypothesis tests

The [Lean 4.35.0 Kernel source](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
can compare arguments under a common regular-definition head, while hints
guide lazy delta unfolding. Here the shared field accessors have `abbrev`
hints and expose projections in one step. The predicted route is reduction
of a `NatTrans.app` projection through the concrete natural transformation
major premise. This is a source-guided inference, not a recorded Kernel
branch trace.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 hints | Tested metadata: both relevant heads are `abbrev`; no same-body regular-hint control was run. Hint contribution is plausible, not isolated. |
| H2 same-head arguments | Tested: only `Eq` left side takes 93.679 s; within `CategoryStruct.comp` only arg 5 takes 96.236 s; within `NatTrans.app` only arg 6 takes 95.717 s. Supported localization. |
| H3 projection/field | Tested: one-step bodies are `Expr.proj`; replacing just the major premise changes 95.869 s to 0 ms, with a 93.567 s reverse control. Strongly supported. |
| H4 dependent domain | Tested on the last four original application arguments: 0/338/0/0 ms. Weakened as the principal site; the final `Eq` type comparison costs 95.520 s. |
| H5 instance paths | Tested corresponding `Eq` carrier and `CategoryStruct.comp` arguments: carrier 2 ms, comp arguments outside the natural transformation at most 1 ms. No independently expensive instance argument at these levels. |
| H6 proof types | The 28-argument proof application checks in 335 ms on replay; no isolated expensive proposition-type pair. Not supported as the primary cost. |
| H7 non-delta | No recursor, cast, or let is the localized pair's outer head. Projection exposure is relevant under H3; a deeper non-delta path remains unmeasured. |
| H8 context/order | In-situ target check 87.6 s and imported final conversion 95.520 s show the same scale. The slight difference can reflect cache and context; no repeated-order matrix was run. |

## Causal record and confidence

The initial final-result pair has a shared `Eq` head; its left composition
contains a shared `NatTrans.app` head but different concrete major premises.
Structural comparison cannot close that subpair. One-step unfolding of the
accessor exposes a projection; aligning the major premise makes the pair
immediate while preserving its checked type. The fixed proof establishes
equality of whole natural transformations before applying the component
lemma, avoiding this concrete component conversion. Because no same-body
regular-hint control or nested-major-premise audit was run, **unfavorable
projection path is strongly supported; whether any unfolding is necessary
within the original major premise is unresolved**.

Confirmed: exact final conversion and timing, head/argument localization,
projection bodies, and major-premise alignment. Strongly supported: concrete
major-premise mismatch beneath an `abbrev` projection drives the 96-second
path. Remaining experiment: audit the nested argument-6 `NatTrans.app` pair.
Overall evidence level: **strongly supported**.
