# Head audit: PR #1627 Weil-sheaf transport

Case ID: `PR1627-powFunctor`. Conversion IDs: `P1627-proof1-id` and
`P1627-proof2-id`. Declaration:
`AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`, including its generated
`_proof_1` and `_proof_2`. Lean 4.35.0, master revision `1ef1fddac73e`.
The baseline is [Before.lean](Before.lean), restored at its original module
identity with the generated Lake setup. All runs use one Lean thread,
synchronous elaboration, normal Kernel checking, `maxHeartbeats=10000000`,
`nice -n 10`, and a 3600-second process bound. `After.lean` is a real,
well-typed same-statement control.

## Expensive conversions and Head Audit

The before prefix takes 107.63 user CPU seconds and 7,781,816 KB peak RSS,
versus 9.38 seconds and 1,837,544 KB after. In-situ Kernel checks introduced
by the old `powFunctor` are 27.8, 55.3, and 14.6 seconds. The source-built
functor value has outer `Expr.app`, head `CategoryTheory.Functor.mk` with eight
arguments and universe parameters `[u+1,u+1,u+2,u+2]`. Its two law fields
are stored generated theorem applications `_proof_1` and `_proof_2`.
[HeadAudit.lean](probes/HeadAudit.lean) finds the target's final inferred
and declared types structurally identical; its value replay takes 13.775 s.
Thus the target's final type pair is not the expensive comparison.

[GeneratedProofAudit.lean](probes/GeneratedProofAudit.lean) reads the two
original generated declarations from the environment. `_proof_1` has nine
type binders, an `Eq` result, eight value binders, and a two-argument `id`
application as its value body. `_proof_2` has 13 type binders, an `Eq` result,
11 value binders, and the same `id` body shape. Their value replays take
20.341 and 33.929 seconds. Both inferred types are structurally identical
to their declared types, and both final conversions take 0 ms.

The original elaborated pair at each localized application site is
reconstructed in [GeneratedProofPrefixes.lean](probes/GeneratedProofPrefixes.lean):
actual is `Kernel.check env lctx` of the `id` proof argument after opening
the stored value's binders; expected is `Kernel.whnf env lctx` of the checked
`id` application prefix, followed by its instantiated Pi domain. Both
outer constructors are `Expr.forallE` for argument 1; the proof term itself
is an `Expr.lam`. The head `id` is a regular definition (its source is a
lambda returning the argument); no `Expr.proj` is the outer body head.
`_proof_1` argument 0 is a proposition with a structurally identical
expected sort: checking it takes 7.588 s, domain comparison 0 ms.
Argument 1 checks in 7.511 s and its actual/expected proposition-type
comparison takes 7.508 s. For `_proof_2`, these numbers are 20.548 s,
0 ms, 14.062 s, and 33.863 s, respectively. The proof types are
definitionally equal; the exact first subterm that makes their comparison
costly is not yet printed.

## Source-guided prediction and hypothesis tests

The `id` argument-1 domain depends on the proposition passed as argument
0, and checking proof irrelevance requires those proposition types to
compare. The recorded `forall` pair cannot be closed by structural identity;
the installed Kernel may reduce definitions inside its dependent domains.
The historical PR described a comparison between `frobeniusPowPullback`
and `WeilSheaf.frobeniusPullback` that exposed `adicLowerStar`, but that
subpair has not been re-extracted from the 4.35.0 proof expressions. Its
relationship to the timed `id` proposition pair is an interpretation,
not an observation of this replay.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 hint order | Not applicable to a demonstrated pair of different reducible heads; the localized value body is the same regular `id` head. No same-body hint control was run. |
| H2 same-head argument | Tested: both `id` applications have two arguments. Argument 0's domain conversion is 0 ms; argument 1's proposition-type conversion is 7.508/33.863 s. Supported as localization, with the first inner differing argument unresolved. |
| H3 projection | No outer `Expr.proj` in the localized `id` bodies. Not applicable at this level; a deeper projection remains possible. |
| H4 dependent domain | Tested with the exact binder domain after argument 0. Argument-1 comparisons take 7.508/33.863 s. Supported as the expensive application boundary. |
| H5 instance paths | Historical PR identifies different concrete functor representations; the 4.35.0 probe has not printed the stored instance leaves. Plausible, not independently supported. |
| H6 proposition types | Tested: generated law proofs have `Eq` types; the `id` proof-argument proposition types, rather than the final declaration types, cost 7.508/33.863 s to compare. Supported. A same-proposition local-variable control remains. |
| H7 non-delta | Raw localized heads are `id`, `forall`, and lambda. No recursor or projection is the outer head. Not supported as primary from current evidence. |
| H8 context/order | In-situ checks are 27.8/55.3/14.6 s; imported-environment value replays are 20.341/33.929 s. Same phase and large scale persist, but exact cache/order effects are unresolved. |

## Causal record and confidence

Initial pairs: the two exact `id` argument-1 proposition types constructed
by the probe. The potentially cheap route is equal proposition types under
the same `forall` structure. They are not structurally identical, so direct
identity fails; which nested parameter first forces reduction is unknown.
The old hand-built `Functor.mk` exposes these concrete functor-law proofs,
whereas the real after term uses the generic `IsoAlgebra.liftOfStr` and
removes their in-situ checks. This control preserves the functor type but
changes the proof construction as a whole, so it does not isolate one
unfavorable unfolding choice. **Necessary versus unfavorable: unresolved.**

Confirmed: the generated proof sites, value-versus-final split, and exact
application-domain timings. Strongly supported: proposition-type comparison
and dependent binder instantiation carry much of the generated-law cost.
Plausible: the historically reported concrete pullback-functor mismatch is
the inner trigger on 4.35.0. Overall causal evidence level: **plausible**.
