# Head audit: PR #1624 integers-sheaf tower iso

Case ID: `PR1624-IntegersSheafHomologyTower`; conversion ID:
`P1624-iso-trans-last-domain`. Declaration:
`AlgebraicGeometry.ProEtale.homologyIntegersTowerIso`. Lean 4.35.0,
master revision `1ef1fddac73e`. [Before.lean](Before.lean) restores the
historical value at its original module path with generated Lake setup;
[After.lean](After.lean) is a well-typed same-statement fixed control.
Probes use one Lean thread, synchronous elaboration, ordinary Kernel
checking, `nice -n 10`, and `timeout 3600`.

## Expensive conversion and Head Audit

The old/new target Kernel checks take 102/3.18 s; whole-prefix CPU takes
111.38/11.77 s with 11,038,208/2,668,464 KB peak RSS. Rechecking the
old stored value in [HeadAudit.lean](probes/HeadAudit.lean) takes 117.578 s.
The first positional inferred/declared type difference is a generated
`_proof_23` versus `DerivedCategory.instHasZeroObject`; it has not been
timed as a proof-proposition conversion and is not assigned causality.

[ValueFrames.lean](probes/ValueFrames.lean) finds nine raw lambda binders,
then 11 let bindings (`Λ`, `fT`, `fY`, `ν`, `e₂`, `e₃`, `e₅`, `Hk`, `fP`, `e₄`,
`e₂₄`). After substituting those original let values, the terminal body is
a seven-argument `Iso.trans` application. Its final two term arguments
are `isoWhiskerRight` and `isoWhiskerLeft`. The latter's independent
Kernel check takes 63.855 s, whereas its exact inferred-type versus
instantiated final binder-domain conversion takes 47.636 s
([IsoTransPrefixes.lean](probes/IsoTransPrefixes.lean)). The preceding
`isoWhiskerRight` term/domain take 19/2 ms.

The final domain pair is obtained by Kernel-checking the original
`isoWhiskerLeft` term, Kernel-checking the six-argument `Iso.trans` prefix,
weak-head reducing that prefix's type to its final Pi domain, then comparing
the two types in the same opened context. Both are `Expr.app`, headed by
the same `CategoryTheory.Iso` constant with four arguments and matching
universes. Their carrier `Functor` and category instance
`Functor.category` are structurally identical, comparing in 0 ms each.
Their source and target endpoints are both headed by `Functor.comp`, and
take 14.706 and 28.640 s respectively
([IsoDomainArguments.lean](probes/IsoDomainArguments.lean)).

The shared `Functor.comp` is a regular definition of Kernel height 1,
whose one-step post-lambda body is `Functor.mk`, as inspected in the
native-pull-tensor control. [IsoCompArguments.lean](probes/IsoCompArguments.lean)
tests all eight arguments of each endpoint. Arguments 0/1 and 4/5 are
structurally identical and compare equal in 0 ms. Arguments 2/3 and 6/7
are not definitionally equal as independent pairs, returning `unequal`
in 0-8 ms. In the target endpoint, argument 6 is a `Functor.comp` term on
the actual side and `higherDirectImageQuotPowTower` on the expected side.
The *whole* endpoints nevertheless compare equal in 14.706/28.640 s.
Thus same-head argument congruence fails before the expensive equality
can be established; reduction of these concrete compositions is necessary
for this representation. The old source builds concrete derived-functor
compositions under two whiskerings; the fixed source passes the pieces to
`homologyIntegersTowerIsoAux` with functor variables.

## Source-guided prediction and hypothesis tests

The [installed Kernel policy](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp)
permits argument comparison under the common regular-definition head and
uses hints to choose lazy delta reductions. The potential cheap route is
`Iso` congruence followed by `Functor.comp` argument congruence. The
endpoints differ structurally, and the tested unequal corresponding
arguments rule out that congruence route in the concrete compositions;
one step of `Functor.comp` exposes `Functor.mk`.
This predicts downstream field comparisons, not an observed first Kernel
branch decision.

| Hypothesis | Status and measured experiment |
|---|---|
| H1 hints | Tested declaration metadata: `Functor.comp` is regular height 1 on both sides. No same-body hint variation was run. Hint asymmetry at this head is not supported. |
| H2 same-head arguments | Tested exact `Iso` domain arguments: carrier/category 0/0 ms; source/target endpoints 14.706/28.640 s. At both `Functor.comp` endpoints, args 2/3/6/7 return `unequal` independently in 0-8 ms. Supported: cheap same-head congruence cannot establish endpoint equality. |
| H3 projection/field | `Iso` and `Functor.comp` are the localized outer heads; one-step `Functor.comp` body is `Functor.mk`, not a projection. No major-premise control at this level; H3 is not supported as the initial cause. |
| H4 dependent domain | Tested exact final `Iso.trans` binder domain after six preceding arguments: 47.636 s; the independent final term check is 63.855 s. Supported, but the independent check also has substantial cost. |
| H5 instance paths | Tested `Iso` carrier and category arguments: both structurally identical, 0 ms. At each `Functor.comp` head, category argument 3 returns `unequal` in 1 ms, alongside other unequal arguments; no isolated instance-only cause. |
| H6 proof types | The selected final argument is an iso term, and the positional `_proof_23` divergence was not separately timed. No supported proof-type mechanism. |
| H7 non-delta | Original value contains 11 lets; after explicitly substituting them, final application-domain comparison still costs 47.636 s. Zeta of those lets is not a sufficient explanation. |
| H8 context/order | In-situ target 102 s and imported value replay 117.578 s preserve the large Kernel cost. Exact cache/order effect is unresolved. |

## Causal record and confidence

The initial checked application pair is the inferred type of the last
`isoWhiskerLeft` argument versus the instantiated seventh `Iso.trans`
domain. Their common `Iso` head reaches two different concrete
`Functor.comp` endpoints, so structural comparison cannot close the
pair. The installed policy permits argument comparison, but args
2/3/6/7 of each composition independently return `unequal`; this
rules out a cheap congruence proof of the whole equality at that head.
Unfolding regular `Functor.comp` exposes `Functor.mk`, after which
concrete object/map fields may need comparison. The fixed auxiliary lemma
changes the representation to variables and avoids the old value check.
**Unfolding is necessary in the original concrete representation**;
whether the Kernel's subsequent path is optimal remains unresolved.

Confirmed: Kernel phase, exact final application-domain pair, common
heads, endpoint timings, and the failed independent argument comparisons.
Strongly supported: concrete derived-functor reassociation forces
unfolding past the shared `Functor.comp` head. Remaining experiment:
measure one-step `Functor.mk` field comparisons after this failure.
Overall causal evidence level: **strongly supported**.
