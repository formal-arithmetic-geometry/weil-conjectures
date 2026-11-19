# EtaleHomComparisonReversedExact workplan experiments

Source snapshot: `etaleHomComparison_reversedExact_commShift_component`,
module `AlgebraicGeometry/Etale/Hom/EtaleHomComparisonModels`, commit
`8ca2e912b93`; Lean and Mathlib 4.35.0. The expensive site is argument
26, `hv`, of `derivedTensorHomShiftComparison_component` after the
preceding 25 actual arguments instantiate the dependent Pi binder.
`probes/HeadAudit.lean` preserves the original application and context.
The actual proposition is `IsEtaleHomTranspose X φ M v`; the expected
proposition is the corresponding quantified tensor-Hom equality over
raw `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A))`.
Normal Kernel checking was used for each helper application; each
application-only probe ends with diagnostic `sorry` **after** that
application. The full `After.lean` theorem is checked without it.

All new timings below used one Lean thread, `timeout 3600`, and
`/usr/bin/time -v`. Kernel-only time and heartbeat consumption are not
separately available. The source heartbeat limit is 200,000.

## B1-P: Initial predicate exposure

EXPERIMENT: B1-P; group: G2-A/G2-B. Hypothesis: unfolding the named
predicate is the necessary first stage, but does not remove the later
argument-domain cost. BASELINE: original application, 28.92 s wall,
27.92 + 1.08 s CPU, 5,495,832 KB RSS, Kernel success but expensive.
CONTROL: `probes/ExpandedHV.lean` presents the same `hv` proposition
as an explicit `forall K` with the named `DerivedCategoryModule`
domain. Only the initial predicate head changes; the same theorem
obligation and helper application remain, with Kernel checking enabled.
`probes/ExpandedHead.lean` confirms that the elaborated actual head is
now `forall`, while the binder domain still first diverges at
`DerivedCategoryModule` versus raw `DerivedCategory`.
RESULT: 28.72 s wall, 27.75 + 0.94 s CPU, 5,480,764 KB RSS in the
head-audit session; same argument-domain conversion remains expensive.
INTERPRETATION: predicate exposure is necessary for the original
representation, but it is insufficient to explain the cost. Confidence:
strongly supported. Exact Kernel reduction order is not observed.

## B1-D: Align only the quantified domain

EXPERIMENT: B1-D; group: G2-C. Hypothesis: the wrapper/raw binder
domain alone accounts for the later cost. BASELINE: B1-P and original
pair above. CONTROL: `probes/wp/RawQuantifiedDomain.lean` changes only
the `hv` binder type from `DerivedCategoryModule A X` to its
definitionally equal raw `DerivedCategory (Sheaf ...)` expression.
The proof construction, equality body, other helper arguments, and
theorem obligation are preserved. Kernel checking is enabled.
`RawQuantifiedDomainHead.lean` confirms the elaborated binder domains
now agree syntactically. Its first printed body difference is in
`sheafIsAbelian`: the generated `EtaleHomLeft._proof_1` versus
`hasSheafify_smallEtaleTopology`. Both prove a `HasSheafify`
proposition, so this first syntactic difference is not by itself
evidence of expensive proof comparison.

`probes/wp/ProofSkip.lean` traverses the same instantiated proposition
pair, ignoring arguments whose inferred types are propositions. It
finds the first remaining data-head mismatch at
`nonproof.body.1.3.5.6.1`: `DerivedCategoryModule` versus raw
`DerivedCategory` inside the equality body. This structural
diagnostic does not purport to trace Kernel execution. RESULT: the
checked application takes 28.92 s wall, 27.88 + 1.10 s CPU,
5,495,128 KB RSS; it remains expensive. The proof-skip diagnostic
takes 28.72 s wall, 28.05 + 0.81 s CPU, 5,715,872 KB RSS and is
not a separate speedup control. INTERPRETATION: binder alignment alone
does not suffice; a nested endpoint mismatch remains. Confidence:
confirmed negative result for the binder-only hypothesis, plausible
causal role for the nested endpoint.

## B1-T: Exact expected proposition control

EXPERIMENT: B1-T; group: G2-B. Hypothesis: presenting the argument at
the helper's exact instantiated expected proposition avoids the
expensive domain conversion. BASELINE: original pair and 28.92 s
application above. CONTROL: `probes/TransportHV.lean` changes only
argument 26 to `fun K => by transport_exact hv K`, preserving all
other helper arguments and the mathematical obligation. The
transported proof proposition, inspected in `TransportHead.lean`,
is syntactically the expected binder domain. The transport proof and
application are normally Kernel checked; the enclosing diagnostic
example ends with `sorry` afterward. RESULT: 3.40 s wall,
2.46 + 1.08 s CPU, 3,181,636 KB RSS. The expensive argument-domain
conversion is removed. The complete fixed declaration in
`After.lean` also Kernel checks (about 3.5 s in the prior audit).
INTERPRETATION: exact proposition alignment is causal, while B1-D
shows that a single top-level binder-domain spelling change is not
enough. Confidence: confirmed for the transport control; the exact
contribution of the later nested endpoint remains unresolved.

## B1-W: Expand the nested wrapper representation

EXPERIMENT: B1-W; group: G2-C/G3-A. Hypothesis: aligning
`DerivedCategoryModule` throughout the supplied proposition
removes the later quantified-domain cost. BASELINE: original
application, 28.92 s wall, 27.92 + 1.08 s CPU,
5,495,832 KB RSS. CONTROL:
`probes/wp/UnfoldAllWrappers.lean` retains the same
expanded `hv` equality and helper application, but a
Lean-level term elaborator performs one delta step on
each `DerivedCategoryModule` application in the
supplied hypothesis type. This is one representation
factor repeated through that proposition; its
definitionally equal theorem obligation and proof term
are preserved. Kernel checking is enabled.
`UnfoldAllWrappersHead.lean` confirms that the
quantified binder is now raw `DerivedCategory`.
`UnfoldAllWrappersProofSkip.lean` traverses the
instantiated pair while skipping proposition-typed
proof arguments. Its first remaining data-head
difference moves from the nested derived-category
wrapper to `EtaleHomLeft` versus `Functor.comp`
at `nonproof.body.3.1.1.3.5`. The immediate body
of the `EtaleHomLeft` abbrev is
`(derivedHom ...).flip.obj M ⋙ scalarExtension φ X`,
so that head can expose a composition.

RESULT: the same normally checked application takes
29.12 s wall, 28.10 + 1.13 s CPU, 5,525,772 KB RSS;
the cost is unchanged. The head and proof-skip
diagnostics take 28.82 s wall, 28.01 + 0.83 s CPU,
5,715,520 KB RSS and 28.82 s wall,
28.07 + 0.88 s CPU, 5,719,296 KB RSS,
respectively; each ends with diagnostic `sorry`
after the helper application. Supports: the wrapper
is one stage of the original comparison, followed
by a functor representation difference. Weakens:
wrapper alignment alone suffices. Unresolved:
which corresponding `Functor.comp` argument
accounts for the retained cost. Classification:
unfavorable nested representation path; confidence:
confirmed negative result for wrapper-only alignment,
plausible for the next functor argument.

## Mechanism

The original regular predicate must expose its quantified body. The
quantified domain initially differs by wrapper/raw representation.
Aligning only that binder exposes a further wrapper/raw difference in
the equality body and leaves the application slow. Expanding the
wrapper throughout the proposition then exposes an
`EtaleHomLeft`/`Functor.comp` difference and is still slow.
Supplying the argument at the exact expected proposition removes
the costly conversion. This supports a dependent proposition
representation problem at multiple levels; the exact
`Functor.comp` argument responsible remains unresolved.
