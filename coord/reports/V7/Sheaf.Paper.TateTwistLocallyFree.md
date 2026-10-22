## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.tateTwist_locallyFree` by a complete
Lean assembly. Its signature, all existing public definitions, their bodies and
the three public imports are unchanged. New proof imports and proved private
helpers supply the compatible root cover, the scalar-extension Kummer map with
its prescribed pure-tensor formula, all finite signed lines, the unbounded finite
inverse functors, and the actual intrinsic integral and rational inverse functors.
The integral and rational opposite object products are constructed explicitly;
the common-stage comparison transports these to the algebraically closed category.

Two separate generic results are stated in new modules:
`Sheaf.Paper.IntegralObjectPullbackLine` and
`Sheaf.Paper.CommonStageTensorLineCoherence`. They isolate the completed pullback
calculation and natural tensor coherence, respectively. Each has its own source,
complete proof in words, blueprint marker and DAG node. The main node's proof and
dependency lists and the theorem's proof docstring follow the implemented route.
No source-library module or consumer is changed. No definition is repaired. The proof-local setup is recorded in
`coord/changes/v7-tate-twist-proof-local-instances.md`.

Validation uses the prescribed compiler and the delivery tool's compilation and
preflight gates. The package compile passed with the two new modules taking 8.9 seconds and
5.2 seconds and the main module taking 54.0 seconds. After localizing the
instance setup, the main module compiled in 40.8 seconds. Its class-alias
linter warnings were addressed with private theorems and instance reducibility;
the delivery tool recompiles this final form. Temporary
profiler, timing commands and diagnostic heartbeat settings are removed. Every Lean line
is at most 100 characters. All original public definitions and the theorem
signature were checked verbatim against the shared source.

## Proved and sorry left

One original hole is closed in
`AlgebraicGeometry.Scheme.tateTwist_locallyFree` (node
`det-def-sp-tate-twist-locally-free`). There is no `sorry` in the item module.
All of its private helpers have complete proofs.

Two holes are added, both in named public theorems with proofs exactly `by sorry`:

- `WeilConjectures.integralObjectPullbackLine`, node
  `lem-pur-integral-object-pullback-line`, in
  `Sheaf.Paper.IntegralObjectPullbackLine`.
- `WeilConjectures.commonStageTensorLineCoherence`, node
  `lem-pur-common-stage-tensor-line-coherence`, in
  `Sheaf.Paper.CommonStageTensorLineCoherence`.

This is a decomposition: one upper hole closed and two independent lower holes
added, not a net proof completion. Existing dependencies may themselves contain
holes; those are used as the stage-3 brief directs and are not modified here.
The new results concern arbitrary integral lines and the common-stage tensor
bifunctor, respectively. Neither restates the Tate-twist theorem: neither asserts
a root cover, Kummer independence, signed Tate object products, nor the integral,
rational and algebraically closed inverse twist functors simultaneously.

## No longer needed

Removed the private imports
`Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` and
`Sheaf.Paper.PadicIntegersInvertEll`. The proof uses the recorded
intrinsic completed coefficients and rational localization directly; it does not
identify them with continuous-function coefficient sheaves first.

Accordingly the main node no longer directly uses
`det-prop-sfb-qlbar-colimit-x-integral-limit` or
`det-prop-sfb-qlbar-colimit-x-invert-ell`. It also no longer directly uses
`def-weil-integral-scalar-extension` or
`lem-sbc-coherent-pair-functor-descent`: the algebraically closed inverse pair is
assembled from natural tensor associativity, the regular unit and opposite object
products. The generic rationalization theorem `lem-weil-twist-rationalization` is also
unneeded: the proof directly localizes the two inverse natural isomorphisms via
`ScalarLocalization.extensionNatIso` and its composition/identity laws. This
avoids extra triangulated-functor hypotheses which the conclusion does not need.
The module `Sheaf.SecSmoothPurity.WeilTwistRationalization` is not imported.
Their five obsolete entries are removed from the main node's
`tool_uses`, preserving the order of all other approvals.

The original direct uses of `lem-poincare-compatible-primitive-roots`,
`def-pur-sheaf-inverse-limit`, `def-pur-sheaf-tensor-product`,
`lem-sfb-localized-site-tensor-restriction`, `def-pur-sheaf-hom`,
`lem-pc-sheaf-modules-tensor-closed`, and
`def-weil-algebraically-closed-coefficients` are replaced in the main proof list by
the existing root/local-model, signed-line and comparison statements which
package these operations. Their mathematics remains in those dependencies.

These are direct-route dependency removals, not claims that their modules have
become globally unreachable. No module is withdrawn or deleted. In particular,
all declarations of the adopted source library remain intact. The unit
`sk-prop-an` has no realized node for this coefficient calculation, and none of
its prescribed purity steps is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement is preserved. Two interface gaps remain in
the available declarations. A basis after restriction to a slice is not itself
an isomorphism for the actual completed derived pullback. That calculation needs
one compatible finite quotient tower and its normalized Roos augmentation, as
recorded in the first new result. Separately, the existing normalized tensor
associators and units are specified objectwise; an equivalence of tensor functors
requires their naturality, supplied by the second new result.

The Kummer isomorphism is proved using the specified root transition and its
scalar-extension adjunct, rather than an arbitrary isomorphism between two
locally trivial lines. Likewise the integral and rational comparisons identify
the actual intrinsic functors. Explicit derived-category universes, extracted
localization isomorphisms and the proved generic `tateTensorInverse` helper keep
the completed constructions from being unfolded repeatedly during elaboration.
Large local comparison isomorphisms use typed `have` bindings. Six proof-only
comparison helpers are proved `Nonempty` lemmas rather than isomorphism-valued
definitions, so later proofs use their witnesses without expanding construction
bodies. Their proofs are complete; this introduces no new mathematical obligation.
Concrete private aliases, registered only as local instances, select the correct
pro-etale site size and sheafification universe before the tensor comparisons
are elaborated. The proposition-valued aliases are private theorems, and the
data-valued alias is instance-reducible. No global instance is added and no
imported instance is removed.
The required change record lists all transitive consumers; none needs adaptation.
The initial delivery attempt stopped at the local compile time limit and pushed nothing; the remote
timing request then received no answer because the server was busy. The packet
was retained and its elaboration optimized. A later preflight required an attribute
change record; the instance aliases are now explicitly local and the negative
instance-attribute commands are removed.

## New nodes

`lem-pur-integral-object-pullback-line` is the generic local calculation for an
arbitrary rank-one integral module with a supplied slice basis. Its proof reduces
the actual completed inverse image to a strictly compatible quotient tower and
the regular completion augmentation. The empty scheme, the zero module category
and the degree-zero regular line obey the same argument. There is no unsupported
noetherian or finite-dimensional-scheme assumption. It is used for each signed
integral line before rational localization.

`lem-pur-common-stage-tensor-line-coherence` concerns arbitrary objects of the
algebraically closed constructible category. It packages natural fixed-right
associativity and the specified untwisted regular unit. Its proof transports the
integral naturality squares through scalar localization and common-stage
representatives. Zero objects, degree-zero twists and repeated coefficient stages
are included by the unit and scalar tower equations. Together with the separately
proved opposite Tate object products it yields the two inverse functor
isomorphisms; it does not assert these object products itself.

Change record: `coord/changes/v7-tate-twist-proof-local-instances.md`.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
