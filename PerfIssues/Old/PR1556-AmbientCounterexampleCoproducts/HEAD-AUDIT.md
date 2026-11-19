# Head audit: PR #1556 ambient coproduct counterexample

Case ID: `PR1556-AmbientCounterexampleCoproducts`; conversion ID:
`P1556-congr-domain`. Declaration:
`AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`.
Lean 4.35.0, master revision `1ef1fddac73e`. [Before.lean](Before.lean)
and [After.lean](After.lean) are well-typed same-statement controls at the
original module path. Probes use generated Lake setup, one Lean thread,
synchronous elaboration, ordinary Kernel checking, `nice -n 10`, and
`timeout 3600`.

## Expensive conversion and Head Audit

Old/new whole-prefix user CPU is 59.47/4.75 s, with 7,760,464/3,056,716
KB peak RSS. The old theorem's in-situ Kernel check takes 54.9 s; the
old closing line is a `simpa` of a whiskered concrete derived-functor
shift-isomorphism component. The fixed line uses `cancel_mono` on a
transformed equality. [HeadAudit.lean](probes/HeadAudit.lean) rechecks the
original stored value in 63.062 s. The theorem has nine outer type
binders and nine value lambdas. Its first raw final-type difference is
metadata versus a `Not` expression; this positional difference has not
been timed as the expensive pair and is not assigned causality.

[ValueFrames.lean](probes/ValueFrames.lean) finds five lets after those
lambdas, then an outer five-argument `Exists.casesOn`. The branch has
two lambdas, then an 18-argument
`DerivedCategory.not_preservesColimitsOfShape_of_forall_hom_ne_zero`
application. Its final argument is a lambda whose body uses another
`Exists.casesOn`; that branch closes with a four-argument `Exists.intro`.
[ClosingSpine.lean](probes/ClosingSpine.lean) preserves this nested spine
without normalizing it. Its presence of recursors is an expression-shape
observation, not evidence that iota reduction caused the cost.

[ClosingPrefixes.lean](probes/ClosingPrefixes.lean) opens these original
branch binders and tests every `Exists.intro` argument against its
instantiated expected Pi domain. Arguments 0-2 Kernel-check in 1, 2, and
2 ms; all three domain conversions take 0 ms. Argument 3 is a proof
lambda. It Kernel-checks in 63.009 s, but its actual/expected domain
comparison takes 0 ms. [ClosingProof.lean](probes/ClosingProof.lean)
opens that lambda's single binder. Its body is a free-variable function
applied to one `id` proof term. The term's own Kernel check takes 62.662
s; its actual and expected types are both `Eq`-headed and the enclosing
application-domain conversion takes 0 ms. [ClosingId.lean](probes/ClosingId.lean)
finds that `id` has two arguments: its `Eq` type argument checks in 2 ms
and compares with its expected domain in 0 ms; its second argument is an
`Eq.mp` proof that checks in 63.535 s, while its instantiated `id` domain
comparison takes 1 ms. Thus the expensive work is inside `Eq.mp`, before
that proof argument's outer type is compared.
[ClosingEqMp.lean](probes/ClosingEqMp.lean) tests the four `Eq.mp` arguments.
Its two `Eq` proposition arguments check in 3/2 ms, the final
`eq_whisker` proof checks in 2 ms, and each expected-domain conversion
takes 0 ms. Argument 2 is a `congr` proof; checking it takes 63.505 s.
[ClosingCongr.lean](probes/ClosingCongr.lean) finds eight `congr`
arguments. Arguments 0-5 check in 0-2 ms and their domains in 0-1 ms.
Argument 6, a `congrArg` proof, checks in 63.514 s and its domain
comparison takes 1 ms. Argument 7, a `zero_comp` proof, checks in 2 ms,
but its inferred proposition type versus the instantiated final
`congr` binder domain takes 50.090 s. Both types are `Eq`-headed. This
is an exact expensive Kernel conversion pair inside the original value.
[ClosingCongrDomain.lean](probes/ClosingCongrDomain.lean) compares its
three `Eq` arguments. The `Quiver.Hom` carrier takes 2 ms; the right
`OfNat.ofNat` side is structurally identical and takes 0 ms. Only the
left `CategoryStruct.comp` pair takes 49.758 s. Both composition heads
are the same `abbrev` field accessor, whose one-step post-lambda body is
`Expr.proj CategoryStruct.2` (also observed in the #1625 audit).
[ClosingComp.lean](probes/ClosingComp.lean) finds seven arguments:
arguments 0-5 compare in 0-1 ms, while argument 6, a `NatTrans.app`
pair, takes 47.366 s. Thus the expensive proposition comparison reaches
one natural-transformation field access.
[ClosingNatMajor.lean](probes/ClosingNatMajor.lean) shows both `NatTrans.app`
terms have the same head and eight arguments. All eight corresponding
arguments compare independently in 0-2 ms; the category instances at
arguments 1/3 and object argument 7 are structurally identical. Argument
6 is a different concrete `Iso.hom` major premise, despite comparing
definitionally equal in 2 ms on its own. Replacing only the right major
premise with the left one Kernel-checks and preserves a structurally
identical result type. The original accessor pair takes 49.548 s, the
aligned pair 0 ms, and original right versus aligned right 50.585 s.

## Source-guided prediction and hypothesis tests

The [Lean 4.35.0 Kernel source](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
can compare arguments under a shared regular head and uses hints for lazy
delta reduction. `id` is a regular definition. The plausible first
inner comparison is the `NatTrans.app` pair under the left composition
of the `zero_comp` proposition and final expected `congr` proof domain.
`NatTrans.app` is also an `abbrev` field accessor whose immediate body
is `Expr.proj NatTrans.0` in the installed environment (as inspected in
the #1625 audit). The prediction is projection exposure of different
concrete natural-transformation major premises, not an observed Kernel
branch trace.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 hints | The enclosing `id` is regular; the localized `CategoryStruct.comp` and `NatTrans.app` heads are `abbrev` field accessors. No same-body regular-hint control was run, so the hint's causal contribution remains plausible. |
| H2 same-head arguments | Tested `Exists.intro`: args 0-2 check in 1/2/2 ms, while proof arg 3 checks in 63.009 s. The `id` proof argument checks in 63.535 s; within `Eq.mp`, only its `congr` proof argument checks slowly (63.505 s). The final `congr` domain pair shares an `Eq` head and costs 50.090 s; only its left composition costs 49.758 s, and only composition arg6 costs 47.366 s. All eight `NatTrans.app` arguments compare independently in 0-2 ms; direct argument mismatch is not the final trigger. |
| H3 projection/field | Tested: the localized `CategoryStruct.comp` and `NatTrans.app` immediate bodies are field projections. Aligning one `NatTrans.app` major premise changes 49.548 s to 0 ms; the reverse control takes 50.585 s, with a structurally identical checked result type. Strongly supported. |
| H4 dependent domain | Tested exact `Exists.intro`, enclosing free-variable, and `Eq.mp` application domains: all measured conversions take 0 ms. The `id` proof-argument domain takes 1 ms. At nested `congr` argument 7, the instantiated domain takes 50.090 s. Supported at that inner boundary. |
| H5 instance paths | At the localized `CategoryStruct.comp` pair, category/instance arguments 0/1 are structurally identical and take 0 ms. At `NatTrans.app`, instance arguments 1/3 are also structurally identical, 0 ms. No expensive instance argument at these levels. |
| H6 proof proposition types | The `id` proof argument is `Eq.mp`, checks in 63.535 s, and has an `Eq`-headed type; its expected-domain conversion is 1 ms. The `Eq.mp` `congr` proof checks in 63.505 s. At `congr` argument 7, the actual and expected `Eq` proposition types compare in 50.090 s. Supported. |
| H7 non-delta | Raw value has five lets and two nested `Exists.casesOn` applications. The 63.009-second cost is inside the final proof lambda; no recursor/iota control identifies a non-delta cause. |
| H8 context/order | In-situ target check 54.9 s and imported-value replay 63.062 s preserve the same slow phase; cache/order effects remain unresolved. |

## Causal record and confidence

The original target value check reaches a final existential proof lambda.
Its `Exists.intro` binder-domain comparison is immediate, so the costly
step is checking the proof itself. That descends to checking an `id`
term applied to the lambda's binder, then to its `Eq.mp` argument and its
`congr` proof argument; each enclosing domain conversion is immediate.
The final `congr` proof argument is different: its `Eq` proposition-type
comparison takes 50.090 s, almost entirely in the left
`CategoryStruct.comp` and its `NatTrans.app` argument. All eight
`NatTrans.app` arguments compare independently in at most 2 ms, but the
accessor is an `abbrev` whose first body exposes a projection of its
concrete `Iso.hom` major premise. Aligning that premise eliminates the
49.548-second cost while preserving the checked type. The fixed proof
uses a different closing construction. **An unfavorable projection path
caused by the differing concrete major premise is strongly supported**;
the exact internal reduction sequence and the independent effect of the
`abbrev` hint are unresolved.

Confirmed: Kernel phase, nested value spine, final proof-argument cost,
cheap enclosing domains, exact 50.090-second `Eq` proposition pair,
the `NatTrans.app` argument audit, and the type-preserving major-premise
alignment. Strongly supported: the concrete whiskered transformation
representation drives an unfavorable projection path. Remaining
experiment: a same-body regular-hint control for `NatTrans.app` to
separate hint effects from major-premise effects. Overall causal
evidence level: **strongly supported**.
