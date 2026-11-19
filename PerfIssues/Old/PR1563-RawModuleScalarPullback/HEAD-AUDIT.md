# Head audit: PR #1563 raw-module scalar pullback

Case ID: `PR1563-RawModuleScalarPullback`; conversion ID:
`P1563-eq-mpr-domain`. Declaration:
`AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula`. Lean
4.35.0, master revision `1ef1fddac73e`. The old and fixed values are
well-typed same-statement controls. Probes restore [Before.lean](Before.lean)
at the original module path with generated Lake setup, one Lean thread,
synchronous elaboration, ordinary Kernel checking, `nice -n 10`, and
`timeout 3600`.

## Expensive conversion and Head Audit

Whole-prefix old/new user CPU is 115.92/50.00 s and peak RSS is
8,008,236/5,146,444 KB. The old target's in-situ Kernel check is 68.2 s;
the fixed target's is 15.2 s. [HeadAudit.lean](probes/HeadAudit.lean)
rechecks the original stored value in 93.833 s. Its final inferred and
declared theorem types are structurally identical, so the expensive
conversion occurs *inside* the value check.

After 12 lambda binders the value is a four-argument `Eq.mpr` application.
`Eq.mpr` is a regular definition with height 1; after its binders, its
one-step body is `Eq.rec`. [ApplicationPrefixes.lean](probes/ApplicationPrefixes.lean)
reconstructs each original application prefix and its instantiated Pi
domain. Arguments 0-3 take 10.630, 33.408, 64.603, and 10.199 s to
Kernel-check individually; their inferred-type/domain comparisons take
0, 0, 0, and 30.254 s. The last argument is `Eq.refl`. For this precise
application boundary, its actual and expected types both have `Eq` heads
with three arguments ([EqMprDomain.lean](probes/EqMprDomain.lean)).
The carrier, headed by `AddCommGrpCat.carrier`, is structurally identical
and compares in 0 ms. The left `CategoryStruct.comp` expression is also
structurally identical and compares in 0 ms. The right
`CategoryStruct.comp` expression differs and compares in 31.026 s.

Both right-hand composition heads are the same `CategoryStruct.comp`
`abbrev`, whose immediate post-lambda body is `Expr.proj CategoryStruct.2`.
Each has seven arguments. [EqCompArguments.lean](probes/EqCompArguments.lean)
finds that arguments 0-6 all differ structurally; their independent
comparison times are 1 ms, 0 ms, 2.245 s, 2.079 s, 2.146 s, 6.601 s,
and 22.155 s. Argument 6 is itself a `CategoryStruct.comp` pair. Thus
the outer composition cost is concentrated in several concrete functor
and morphism arguments, especially a nested composition; the first
unfavorable reduction inside that nested pair remains unmeasured.

## Source-guided prediction and hypothesis tests

The [installed Kernel policy](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
uses head metadata for lazy unfolding. The common `Eq` head lets the
comparison reach its third argument; the common `CategoryStruct.comp`
accessor can then expose a projection from concrete category structures.
The historical source includes a concrete `higherDirectImageRawOverFunctor`
path and an `unop (op B)` term, whereas the fixed helper works through a
raw pullback. These are source-guided candidates, not a printed first
Kernel reduction step.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 hints | Tested metadata: `Eq.mpr` regular height 1, `CategoryStruct.comp` abbrev. No same-body hint matrix; an unfavorable order is plausible, not confirmed. |
| H2 same-head arguments | Tested: in the final `Eq` domain only right argument 2 costs 31.026 s; within its `CategoryStruct.comp`, argument 6 costs 22.155 s and arguments 2-5 cost 2.079-6.601 s each. Supported as localization. |
| H3 projection/field | Tested one-step body: `CategoryStruct.comp` exposes `Expr.proj CategoryStruct.2`. A major-premise alignment control has not been run, so causal role is plausible. |
| H4 dependent domain | Tested exact `Eq.mpr` prefixes: only argument 3's instantiated domain costs 30.254 s; its independent value check takes 10.199 s. Supported at this boundary. |
| H5 instance paths | Tested comp argument 1, `Category.toCategoryStruct`, in 0 ms; category argument 0 in 1 ms. No expensive instance subpair at this level. |
| H6 proof types | The last proof argument is `Eq.refl`; its `Eq` proposition type/domain comparison takes 30.254 s. Supported as the precise proof-type boundary, with the cost located in the right composition. |
| H7 non-delta | `Eq.mpr` unfolds to `Eq.rec` in one step, so recursor reduction is possible. The measured final domain pair is an `Eq`/`CategoryStruct.comp` comparison; no recursor reduction trace isolates H7 as the primary cost. |
| H8 context/order | In-situ target 68.2 s versus imported value replay 93.833 s. Both are large Kernel costs; cache/check-order sensitivity is unresolved. |

## Causal record and confidence

The initial application-domain pair compares the actual type of `Eq.refl`
with the fourth `Eq.mpr` binder's instantiated expected domain. Their
common `Eq` head exposes a differing right `CategoryStruct.comp` term.
Direct structural identity fails at all seven composition arguments;
several individually require seconds of conversion. The `abbrev`
composition accessor exposes a projection in one step, but current probes
do not distinguish projection reduction from work inside its differing
arguments. The fixed helper changes the proof construction and avoids
this old `Eq.mpr` value. **Necessary versus unfavorable: unresolved.**

Confirmed: value/final split, exact dependent-domain pair, common heads,
argument timings, and one-step body shape. Plausible: concrete functor
representation causes avoidable projection work. Remaining experiment:
align one nested composition major premise while preserving the checked
type. Overall causal evidence level: **plausible**.
