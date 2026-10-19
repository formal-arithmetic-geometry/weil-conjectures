## Worker report

Repair of the independent return on immutable head 79250a4687c4. The first resumed
dry run of the saved packet passed (90c3302328); it was not pushed because the
mathematical return points F1–F3 were still present. This delivery repairs them.
Only the item's module and its `lean` record are delivered. The node was reread
from the current shared DAG; its statement, hypotheses and dependency lists are
unchanged. All definitions have actual bodies; postponed named theorems have
source and proof-plan docstrings and belong to this item's construction.

F1: removed the dependency module and dependency node copy. The item imports
`Sheaf.Paper.SfCommonStageDirectImage`, preserving N5's fourteen sfModel*
declarations and both live importers. The three arbitrary-field declarations
`arbitraryFieldPullback_isLeftAdjoint`, `arbitraryFieldDerivedPush`, and
`arbitraryFieldDerivedAdjunction` now belong to the item module. The right
adjoint is determined by the actual common-stage inverse image and its
adjunction, not by an arbitrary functor witness.

F2: removed `Properties.shiftF`, `Properties.shiftR`, and `Duality.shift`.
`pushShift` is `ordinaryAdjunction.rightAdjointCommShift`, using the actual
`fieldCommonPullShift`. `shriekShift` is the composite of the open adjunction's
`leftAdjointCommShift` and the proper image's `pushShift`. No shift is selected by
transport along exchange. `Rational.homShift` explicitly localizes the recorded
`podIntegralHomShift`, including the localization comparisons in both inputs.
That comparison is fixed by the signed Hom-complex product reindexing, with
factor (-1)^(a*k). `homShift_existsUnique` specifies the common-stage comparison
by naturality and its image at EVERY rational coefficient field, conjugated by
the evaluation-normalized `homInclusion`. `dualShift` is its inverse source shift
with the canonical zero-shift comparison on omega. `ShiftCompatible` now uses
these definitions directly and has no shift-data arguments.

F3: replaced the old naturality-at-inclusionTransition equation.
`Rational.Datum.exchange` is the rational-stage version of the same three
projection/evaluation/trace adjunction transposes. `ScalarCompatible` states
that its image under the stage-E inclusion agrees with `Datum.exchange` on the
included object, after the specified inclusion comparisons. These comparisons
are constructed, not fields: `pullInclusion` is the recorded pair formula;
`pushInclusionArrow` is its ordinary counit mate; `openInclusionArrow` is its open
unit mate; `shriekInclusion` composes them. `omegaXInclusionArrow` and
`omegaYInclusionArrow` transpose the included rational traces, using the
canonical coefficient-unit comparison. `dualXInclusion` and `dualYInclusion`
combine these with evaluation-normalized Hom inclusion. The helper invertibility
theorems assert the usual scalar comparisons of these specified maps. The scalar
condition is imposed at every finite stage, including any larger field and the
identity field, and therefore refers to the actual rational exchange rather
than an arbitrary morphism family or the naturality of the common exchange.

Hypothesis and conclusion correspondence:

- A field k is `{k : Type u} [Field k]`; a prime invertible in k is `(l : ℕ)
  [Fact l.Prime] (hl : IsUnit (l : k))`. The algebraic closure is `(Ω : Type v)
  [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]`, with independent u,v.
- X,Y are `Scheme.{u}` with `Over (Spec (.of k))`. Each structure map has
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`; the last two mean
  finite type. The morphism f has `IsOver`, `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, exactly as the node states.
- The categories are literally `generalAlgebraicallyClosedConstructibleCategory`,
  the carrier of `intrinsicPbcQbarCategory`, with its published shifts and
  distinguished triangles. There is no substitute category or envelope.
- `tensor`, `pull`, `hom` use `commonStageDerivedTensor`,
  `commonStageDerivedPullback`, and `commonStageDerivedInternalHom`.
  `Closed.permitted` asserts internal-Hom constructibility for all pairs.
  `Closed.tensor_eq`, `unit_eq`, `symmetry_eq` and `evaluation_eq` fix tensor,
  the coefficient unit, Koszul symmetry and evaluation to the recorded maps.
  `evaluationAtStage` is the actual rational completed evaluation transported
  through the normalized tensor and Hom comparisons at a common finite field.
- `Factorization` is a compactification with the inherited k-structures.
  `openExtension` is left adjoint to actual restriction; `support` composes it
  with proper ordinary image; `shriek` applies this to the compactification.
  `Properties.compactF`, `compactY` and `compactX` identify these functors
  (objects AND arrows) with `SfCompactSupportCoefficientAction.system.functor`
  for f, a_Y and a_X respectively.
- `Datum.adjY` is the adjunction for a_Y compact support. `adjX` is for f!
  followed by a_Y!, identified with a_X compact support by `compactX`.
  `omegaX/Y` apply these right adjoints to the specified base coefficient unit.
  `dualX/Y` are the recorded internal Hom into those objects.
- `relativeResidueFieldAlgebraMap` uses the structure-induced residue-field map;
  `relativeTranscendenceDegree` is `Algebra.trdeg` for that algebra structure.
  `Normalization` identifies omega with the pulled-back base unit for a
  structure isomorphism and, on every irreducible smooth open of relative
  generic transcendence degree d, with the Tate coefficient `(d)[2*d]`.
  `Properties.normalizedX/Y` impose these signs and relative normalization.
  On singular schemes omega is still pinned by a! of the base unit.
- `Duality.equivalence` is anti-equivalence. `Duality.exact` says it carries
  distinguished opposite triangles to distinguished triangles.
  `bidual` is `CategoryTheory.ringedSiteBidual`, the transpose of swapped
  evaluation; `Duality.bidual_isIso` and `bidual_natural` concern this very arrow.
  `dualShift` supplies `D(K[n]) ≅ D(K)[-n]` by the normalized Hom shift.
- `arbitraryFieldDerivedPushWithUnit` is the ordinary adic right adjoint.
  Its endpoints, and those of `shriek`, are bounded constructible categories,
  so they express preservation of bounded constructibility for both images.
- `properProjection` is the ordinary counit mate of canonical tensor pullback;
  `openProjection` is the open unit mate. `supportProjection` composes open
  projection and inverse proper projection. `Datum.pairing` adds evaluation
  and the a_Y trace, and `Datum.exchange` is its structure-adjunction,
  closed-Hom and ordinary-image transposes. `Properties.exchange_isIso`
  asserts this canonical map is invertible; `exchange_natural` is its naturality.
- `Properties.shift_compatible` is the square using the fixed shifts described
  in F2. `scalar_compatible` is agreement with the rational-stage exchange via
  the fixed inclusion comparisons described in F3. They concern the same map
  as `exchange_isIso`; no comparison is selected to force these equations.

Dependencies and declarations read and used:

- `def-weil-scheme-morphism-properties` is the convention node; its Mathlib
  `Scheme.Over`, `Scheme.Hom.IsOver`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsOpenImmersion`, `IsProper` are used directly.
- `Sheaf.Paper.IntrinsicQbarCategory.intrinsicPbcQbarCategory` is the recorded
  alias for the literal common-stage carrier used here.
- `Sheaf.Paper.QcqsCompactSupportRealization.sfQcqsCompactSupportRealization`
  retains the completed proper/open realization; the common-stage action is
  `SfCompactSupportCoefficientAction` in
  `Sheaf.Paper.CompactSupportCoefficientAction`.
- `Sheaf.Paper.DerivedPullbackTensorHom` supplies the three common-stage
  operations, rational operations, object formulas and scalar comparisons.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic.Algebra.trdeg` and
  `Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Spec.residueFieldIso`) give the dimension function.
- `Sheaf.Paper.SfCommonStageDirectImage.sfModelDerivedPush` retains the landed
  finite-field interface, publicly reexporting the completed direct-image
  construction. Its `FiniteFieldDatum` binder prevents direct application to
  arbitrary k; the item-local right-adjoint extension supplies that case.
- `Sheaf.Paper.FieldWeilShriekShiftData.fieldCommonPullShift` is the prescribed
  common-stage pullback shift; Mathlib's shift adjunction API constructs mates.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation.podIntegralHomShift` is the
  signed Hom comparison fixed on ambient completed-ring complexes. The
  integral and rational inclusion CommShift instances are the published ones.
  `homInclusion` uses the same coefficient evaluation, not a second Hom notion.

Edge cases: empty X or Y does not introduce a point-existence or irreducibility
hypothesis. Smooth-chart conditions are internal quantifiers; disconnected and
singular schemes are included. At Spec k, the structure adjunction pins omega to
the unit. On smooth relative affine d-space the normalization is `(d)[2*d]`.
Shifts include n=0 and negative n; the signed comparison includes a=b=0.
The finite-stage equation includes the base coefficient field, repeated fields,
and objects obtained after ANY finite extension. Rank-zero objects are included.
Arbitrary imperfect k and k=R,l=2 satisfy the hypotheses; no finite Galois
cohomological dimension, separable closedness or positive characteristic is added.
The coefficient universe v is independent of the scheme universe u.

Searches: the saved packet's `msearch.py` LeanFinder searches for relative
Verdier duality/direct image over arbitrary fields returned generic functors,
no exact match; Loogle `Verdier, dualizing, constructible` returned no hits;
Mathlib grep `Verdier|dualizing|bidual` found no exact theorem. Upstream and
shared `rg` searches found finite-field `coef_qbar_verdier` and generic
coefficient packages, not this arbitrary-field statement. This repair searched
`fieldCommonPullShift|CommShift|signed`, `HomShift|Shift.*Hom`,
`rational.*Tensor|canonical.*PullbackTensor`, `projection|Projection` and
`UnitInclusion|CommonUnit` across the named shared modules. It reused the
published canonical shift, integral signed Hom and tensor inclusion formulas;
it did not invent replacement underlying operations. The source remains the
local Bhatt–Scholze PDF §§6.7–6.8 and the node's relative BBD/ILO normalization.
No statement correction or STATEMENT-DISPUTED flag is needed.

## Second reading by Q08

This is an in-thread rereading, as the dispatcher prohibits starting other agents.
I opened the current node and the repaired file and checked the above hypotheses
and every conclusion against them. The first resumed dry run's success was only
a mechanical success and did not fix the returned defects. F1 is now repaired
by preserving the existing dependency record and importing its module. F2 is
repaired by deleting the free shift fields and using adjunction mates and the
signed integral-Hom normalization at every rational stage. F3 is repaired by
comparing two independently defined exchanges, common-stage and rational-stage,
through explicit inclusion maps built from evaluation and traces. In particular
`exchange_natural` alone no longer proves the scalar condition.

The exchange, bidual, a!-defined omega, trdeg normalization and all scheme/field
hypotheses of the returned head were retained. The extra rational-stage and
inclusion declarations expose parts of this same construction, not additional
hypotheses on the main theorem. No dependency node is re-recorded. Every added
postponed theorem describes its construction and its proof plan in its docstring.

Validation: `scompile.py` checked the repaired module both as a sandbox module
(43.3 seconds) and under its final library name (47.2 seconds), with no errors or
warnings. The final required `deliver2.py --no-push` passed preflight and compiled
all delivery-owned files: `OK (dry run): commit b87cddf1ee ... nothing pushed`.
The packet contains one Lean module and the item node; its only difference from
the current shared node is `lean`. All 96 named declarations have docstrings,
and every line meets the 100-character bound.
