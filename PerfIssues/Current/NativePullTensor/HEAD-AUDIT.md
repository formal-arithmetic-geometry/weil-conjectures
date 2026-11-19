# Head audit: native pull tensor

Case ID: `NativePullTensor` / `nativePullTotalTensor` (the same 23-second
conversion recurs in three adjacent declarations). Conversion IDs: `NPT-choose-1`,
`NPT-choose-2`, `NPT-result`. Lean 4.35.0; master revision `1ef1fddac73e`.
The original source is the master build tree; all probes use one Lean thread,
synchronous elaboration, ordinary Kernel checking, `nice -n 10`, and a 3600-second
process bound. The imported declaration's value and type are the original
elaborated expressions, not reconstructed source terms.

## Expensive conversion and Head Audit

The original declaration checks in 268.39 CPU seconds as a module, versus 6.16
with Kernel checking diagnostically disabled. Direct replay separates the
`nativePullTotalTensor` value check (47.457 s) from its final inferred/declared
type conversion (23.422 s). [ValuePrefixes.lean](probes/ValuePrefixes.lean)
opens the 12 original value binders and checks the three arguments to
`@Exists.choose.{u+3}`. The predicate argument's inferred type and its
instantiated binder domain are both `Iso ... -> Prop` but have distinct
elaborated concrete functor/instance subterms: `Kernel.isDefEq` takes 23.012 s.
The existential proof argument has actual/expected domains `Exists ...` under
the same instantiated predicate: 23.065 s. Each argument itself checks in
at most 6 ms. These are application-domain comparisons, not proof checking
of the arguments.

For `NPT-result`, [HeadAudit.lean](probes/HeadAudit.lean) and
[PairArguments.lean](probes/PairArguments.lean) define the exact pair without
normalization: actual is `Kernel.check env lctx body`, where `body` is the
stored value opened at its 12 lambdas; expected is the stored declared type
with those same 12 arguments substituted into successive Pi binders. Both
outer constructors are `Expr.app`, with the identical
`CategoryTheory.Iso.{u+2,u+2}` head and four arguments (functor type,
category instance, source endpoint, target endpoint). The inferred and
declared result spines both use `Functor.comp` for their endpoints. No
projection or recursor is the outer head of this pair. Universes agree at
the `Iso` head.

The first two `Iso` arguments compare in 1 ms each. The source and target
endpoints take 11.453 and 11.390 s. [EndpointArguments.lean](probes/EndpointArguments.lean)
shows both endpoint heads are `Functor.comp`, a regular definition of Kernel
height 1 whose immediate body, after its lambda binders, is `Functor.mk`.
For the source composition, arguments 0-5 and 7 compare in 0-2 ms; argument
6, headed by `Functor.obj`, takes 11.346 s. For the target composition,
arguments 0-6 compare in 0-1 ms; argument 7, also `Functor.obj`, takes
11.240 s. The other category and instance arguments at this level are cheap.

[ObjectArguments.lean](probes/ObjectArguments.lean) audits those two
`Functor.obj` applications. Each has six arguments, with the same
`Functor.obj` head and corresponding `Functor.uncurry` functor argument.
All six arguments compare independently in 0-1 ms on both endpoints; the
object (`nativeTensorTotal`) is structurally identical. Thus the 11-second
cost is at the enclosing field/application comparison, not any one
independently timed argument. [KernelDiff.lean](probes/KernelDiff.lean)
also finds a generated `_proof_3` versus `Sheaf.monoidalPreadditive` as the
first positional difference in the full final pair. That positional result
is not a timed proof-proposition comparison and is not assigned causality.

[MajorAlignment.lean](probes/MajorAlignment.lean) verifies that replacing
only the right `Functor.obj` application's functor argument with the
definitionally equal left argument leaves the result type structurally
identical and Kernel-checks. Both original object pairs take 11.396/11.355 s;
both aligned pairs take 0 ms. Comparing the right original with its aligned
version takes 11.284/11.301 s. [HintControl.lean](probes/HintControl.lean)
then defines a regular `def` and an `abbrev` with the same `F.obj X` body,
remaps their universe and binder spines, and Kernel-checks every variant.
On the first endpoint, original raw `Functor.obj` takes 11.388 s,
same-body regular/regular 0 ms, same-body abbrev/abbrev 11.251 s,
regular/raw 11.295 s, and abbrev/raw 11.299 s. This is a controlled
H1.1/H1.2 matrix on the same conversion shape and concrete arguments.

## Source-guided prediction

The [installed 4.35.0 Kernel policy](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
tries an argument comparison for equal regular-definition heads and uses
Kernel reducibility hints for lazy delta reduction. `Functor.obj` has the
`abbrev` hint, and its immediate post-lambda body is the actual
`Expr.proj CategoryTheory.Functor.0` ([HintControl.lean](probes/HintControl.lean)).
The same-body regular control is immediate, whereas the abbrev and raw
controls are slow. This predicts that the `abbrev` path exposes the
projection field of a concrete `Functor.uncurry` major premise. At the
outer level, one-step `Functor.comp` unfolding exposes `Functor.mk`, with
dependent object and map fields. The in-situ
diagnostic counters (1.10 million `Functor.obj` and 463,500 `Functor.map`
unfolds in the first check) are downstream observations, not evidence of
the first internal Kernel decision. The exact internal reduction sequence
is not traced.

## Hypothesis tests

| Hypothesis | Status and measured experiment |
|---|---|
| H1 reducibility hint | Tested with same-body controls: regular/regular 0 ms; abbrev/abbrev 11.251 s; regular/raw 11.295 s; abbrev/raw 11.299 s, all well typed. The regular-hint optimization is a confirmed contributor. |
| H2 same-head argument | Tested. `Iso` arguments 0/1: 1/1 ms; endpoint arguments 2/3: 11.453/11.390 s. At `Functor.comp`, only `Functor.obj` arguments 6/7 take 11.346/11.240 s. All six arguments of each `Functor.obj` compare in 0-1 ms individually, so a *failed* argument comparison is not the trigger at that last level. |
| H3 projection/field | Tested. The surface head is a `Functor.obj` constant application, but its immediate body is `Expr.proj Functor.0`. Aligning only the definitionally equal functor major premise changes 11.396/11.355 s to 0 ms; right/original versus right/aligned remains 11.284/11.301 s. Supported. |
| H4 dependent binder | Tested. The exact `Exists.choose` binder domains after preceding arguments are applied cost 23.012/23.065 s; independent argument checks cost at most 6 ms. Supported as the location and amplifier of the value check. |
| H5 instance paths | Tested at the `Iso`, `Functor.comp`, and `Functor.obj` spines: corresponding category/instance arguments compare in 0-2 ms individually. A concrete instance appears in the first positional full-type diff, but its causal role remains unresolved. |
| H6 proof irrelevance | The first structural `_proof_3`/instance difference was inspected; proposition types were not independently compared. Unresolved, not supported as a cause. |
| H7 non-delta | No outer lambda/let/recursor/projection at the localized endpoint pair. `Eq.rec` appears in downstream counters, but no recursor path was isolated. Not applicable as an established primary cause. |
| H8 context/order | Diagnostic replay gives 23.422 s final conversion, matching 23.012/23.065 s binder-domain conversions and the earlier 23.167 s cross-type replay. Self-comparisons finish in 0 ms. This supports the scale of the isolated conversion; cache/order effects remain possible. |

## Causal record and confidence

Initial pair: inferred versus declared `Iso` result under the same 12
binders; the `Exists.choose` domain pairs expose the same 23-second scale.
Potential high-level route: compare the shared `Iso`, `Functor.comp`, and
`Functor.obj` heads and their corresponding arguments. The `Iso` and
`Functor.comp` levels identify a costly `Functor.obj` subpair. Its six
arguments are independently cheap, but `Functor.obj` is an `abbrev`; the
installed policy's same-regular-head optimization does not apply to it.
The first `Functor.obj` body exposes a projection of a concrete
`Functor.uncurry` major premise. Aligning that premise removes the cost,
as does keeping the same body under a regular `def` on both sides. The
recorded unfold counters show subsequent concrete functor/category activity.
The controlled variants preserve the types and the definitional equality
obligation. **Unfavorable unfolding path** caused jointly by the abbrev
field accessor and the different elaborated functor-major-premise terms.
This is an inference from source policy and controls, not a direct trace
of the Kernel's branch decisions.

Confirmed: Kernel phase, exact application-domain comparisons, endpoint
localization, projection body, the well-typed same-body hint matrix, and
major-premise alignment. Strongly supported: the inferred unfavorable
projection path under the installed policy. Unresolved: the exact sequence
of subsequent Kernel reductions and whether `_proof_3`'s proposition type
contributes separately. Overall evidence level: **confirmed for the
abbrev/major-premise causal factors**.
