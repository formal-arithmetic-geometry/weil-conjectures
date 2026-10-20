## Worker report

This delivery attaches existing declarations; it introduces no Lean module, definition,
proof, or statement correction. The node itself identifies its content with the concrete
interface `fix-prop-projection-formula` (also `blueprint.same_as`). That node already owns
`lean/Sheaf/Paper/CompactSupportProjectionFormula.lean`. I read its declarations and
all four statement-dependency records and their declaration signatures and docstrings.
There is no repair note at `coord/repair-notes/sk-rem-sf-pf-done.json`.

The primary declaration is `WeilConjectures.compactSupportProjectionFormula`, lines
111--136 of that module. The attachment also lists the existing declarations which
supply its coefficient and Weil clauses. Recording only the primary declaration would
conceal those clauses, so `lean.declarations` lists the complete relevant interface.
`lean.statement` is copied verbatim from the primary theorem's source, excluding `:= by`.

The following is the clause-by-clause match with the unchanged DAG statement.

- The global finite-field data are `D : FiniteFieldDatum.{u}`; the distinct coefficient
  prime and chosen algebraic closure are in `C : D.CoefficientDatum`. The extension is
  `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, and
  `[FiniteDimensional (Padic C.l) E]`. Positive finite quotients use `n : ℕ`, `hn : 1 ≤ n`.
  These are exactly the binders of the primary declaration and the operation datum.
- Concrete operations are `S : SixFunctorOperationDatum D C E n hn`, the recorded
  declaration of `def-fix-six-functor-datum`. It carries normalized construction data;
  no projection-isomorphism axiom or abstract six-functor law is a theorem hypothesis.
- Finite-type k-schemes are `X Y : SixFunctorSpace D`. In both projection-law records,
  the morphism `f : X ⟶ Y` has `[IsSeparated f.hom.left]`,
  `[LocallyOfFiniteType f.hom.left]`, and `[QuasiCompact f.hom.left]`.
  The arbitrary `c : Compactification f.hom.left` presents the canonical operation,
  with equality under comparison explicitly included; it is not a properness assumption.
- At finite coefficients, the first conjunct is
  `CompactSupportFiniteProjection.Laws S.toSixFunctorFiniteOperations`.
  Its `isIso` field quantifies `K : sixFunctorFiniteCategory D C E n hn X` and
  `L : finiteTorConstructibleCategory C.l E n hn Y.obj.left`. Thus K is arbitrary
  bounded constructible, and only L has the stated finite-Tor condition.
- The displayed arrow is `CompactSupportFiniteProjection.component S ... K L` at
  finite coefficients and `compactSupportProjectionComponent A f c K L` at the
  higher stages. Their signatures have source `(Rf! K) tensor L` and target
  `Rf! (K tensor pull L)`. I read their definitions in
  `Sheaf.Paper.ConstructibleProjectionMates`: they are the specified projection
  component, with the finite version transported through the normalized realization.
  The theorem asserts `IsIso` of this actual arrow, not existence of an unrelated iso.
- Integral coefficients are the second conjunct
  `CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
  S.higher.integralExchange S.integralFiniteTorDomain`.
  The category is the actual complete constructible category; the second-domain
  predicate is `finiteTorConstructibleIntegral`, as defined by the dependency datum.
  K again has no finite-Tor predicate in the law's `isIso` field.
- E coefficients are the third conjunct, with `S.higher.rational`, its tensor and
  exchange. Algebraically closed coefficients are the fourth, with
  `S.closure.commonStage`, its tensor and exchange. The domain `fun _ _ ↦ True`
  expresses the existing field-coefficient convention that every bounded constructible
  object has finite Tor amplitude, not an omitted finite-level condition.
- The remaining primary conjuncts quantify every positive normalized finite level
  and every `E₀ : Padic.FiniteCoefficientFields C.l C.Qbar`, with its integral,
  rational and finite-level laws. They support the stated common finite-stage model.
- Naturality in K and L, compactification comparisons, composition, the associativity
  pentagon, and proper coincidence are respectively the `naturality`,
  `compactification`, `composition`, `pentagon`, and `proper` fields of both
  `CompactSupportFiniteProjection.Laws` and `CompactSupportProjectionLaws`.
  I read both records in `ConstructibleProjectionMates.lean`, lines 154--222 and
  499--567. In particular the `proper` field has `[IsProper f.hom.left]` and
  compares exactly with `compactSupportProperProjection`/`properComponent`.
  It supplies no ordinary-direct-image projection formula for nonproper f.
- Finite reduction and scalar extension are stated by
  `compactSupportProjectionFormula_coefficients`, lines 195--228. Its four
  conjuncts are positive finite quotient changes, completed-to-finite reduction,
  integral scalar extension, and finite scalar extension with ramification.
  The first two restrict to the stated finite-Tor domains (both inputs where
  reduction requires them). This does not restrict the separate finite-stage
  isomorphism to finite-Tor K. Rational/common-stage scalar comparisons are the
  localized/included normalized comparisons of the operation datum, as the theorem
  docstring explains; no reduction of an arbitrary field object is claimed.
- The sites and coefficient models are inherited from these very operation functors:
  finite intrinsic pro-etale realization, completed integral tensor/pullback,
  rationalization, and common-stage inclusion. No etale replacement category is
  silently substituted for the stated pro-etale coefficient categories.
- The additional Weil hypotheses are explicit in the existing namespace binders:
  `X₀ Y₀ : Over (Spec (.of D.k₀))` with separated, locally finite-type and
  quasi-compact structure maps, and `f₀ : X₀ ⟶ Y₀` with the same morphism
  properties. `D.geometricFiber` and `zlFiberMap` give precisely their geometric
  base changes. These hypotheses are confined to the Weil declarations.
- `CompactSupportWeilProjection.restriction` states the unique equivariant
  projection iso with its forward arrow equal to the actual proper/open component.
  `CompactSupportPbcProjection.forward` and `.iso` transport it into exactly
  `WeilD` from `def-wf-weil-category`, retaining arbitrary rational Weil maps.
  The parameters F, WX, WY are the published normalized coefficient/Frobenius
  comparisons, not projection invertibility or integral Weil lifts.
- `CompactSupportPbcProjection.tensor_identification` states both equality of the
  ambient carrier with the `wfTensor` object and HEq of the structure morphism
  with `wfTensorFrobenius`, the recorded declaration of `def-wf-tensor-product`.
  The comparison is fixed by `tensorComparisonArrow`, including normalization
  on integral representatives and the finite-counit cancellations. This checks
  the tensor Frobenius as well as the coefficient-category presentation.
- `CompactSupportPbcProjection.commonIso` gives the actual iso in `WeilDQbar`,
  after extension of the two arbitrary input objects to any common finite field.
  Its `hK : K.stage ≤ E₀` and `hL : L.stage ≤ E₀` include identity extensions.
- The final discharge sentence introduces no further mathematical object or law:
  these are exactly the interface's obligations. The no-duality sentence is a
  provenance assertion (the node's proof step 5 explicitly says so), rather than
  an extra proposition with an unspecified meaning. The existing theorem docstrings
  follow finite projection, finite reduction, completion/Nakayama, localization,
  common stages and proper/open mate pasting; they do not invoke Verdier duality.
  This stage-2 attachment does not claim the existing sorry proofs are already proved.

Dependency declarations used: `Sheaf.Paper.SixFunctorOperationDatum`,
`WeilConjectures.SixFunctorOperationDatum`; `Sheaf.Paper.CompactSupportProjectionFormula`,
`WeilConjectures.compactSupportProjectionFormula` and the listed companions;
`Sheaf.Paper.PbcWeilCategory`, `WeilConjectures.WeilD` and `WeilConjectures.WeilDQbar`;
`Sheaf.Paper.WeilTensorProduct`, `WeilConjectures.wfTensorFrobenius`.
The latter's full signature and its mu-then-tensor definition were read.

Edge cases checked: n=1 is included, n=0 is excluded exactly as the source requires;
empty schemes, zero objects and identity morphisms are not excluded. Finite K can
have infinite Tor amplitude (e.g. the residue module over O/varpi²), because only L
lies in the finite-Tor subcategory. No finite-field descent model is required outside
the Weil clause. Arbitrary rational Frobenius maps need no integral lift. Equal
coefficient fields and arbitrary common larger fields remain allowed. A nonproper
map receives only the compact-support formula. The existing universe u is explicitly
bound, with the site's object/morphism sizes inherited unchanged from the datum.

Searches actually performed on 2026-10-20:

- `msearch.py ... leansearch "Compact support projection formula for bounded
  constructible derived sheaves"`: eight unrelated compactly supported function
  results (including `hasCompactSupport_def`), no exact Mathlib match.
- `msearch.py ... leanfinder "The canonical compact support projection formula is
  invertible for bounded constructible sheaves and finite Tor second input at finite
  integral rational and algebraically closed coefficient stages, compatibly with
  composition and Weil Frobenius"`: eight results, including scheme section
  localization and light condensed tensor criteria; no exact match.
- `msearch.py ... loogle '"projection", "Sheaf"'`: zero hits.
- `msearch.py ... grep "projectionFormula|projection_formula|CompactSupportProjection"
  CategoryTheory`: zero hits.
- `rg` in `lean/WeilConjectures` for the item id, projection-formula names and
  `CompactSupportProjectionLaws`: no item attachment; various finite/proper etale,
  pro-etale and module projection results, not this entire four-stage interface.
- `rg` in `lean/Sheaf` for `compactSupportProjectionFormula`, discharge names and
  the item id found the exact existing interface module. I read its primary theorem,
  coefficient theorem, Weil declarations, their docstrings and the law records.

No new nodes, dependency repairs, statement corrections or unresolved statement faults.
No `.lean` file is delivered, so the existing-attachment rule in brief-stage2 §1
requires no new compilation; the prescribed delivery dry run validates the attachment.

## Second reading by NG

As the dispatcher assigned one worker and explicitly forbids other agents, this is a
separate second reading by the same worker, not a claimed independent review.
I reopened the node and compared its four paragraphs against the declarations above.
The primary theorem alone lacks the separately stated coefficient and Weil clauses;
those companion declarations are therefore explicitly attached in `lean.declarations`.
The finite first input remains all of Dbc, and the reduction qualification stays local
to its reduction assertions. Both kinds of projection-law records retain the specified
forward arrow and all six coherence fields. The rational Weil restriction uses the
actual PBC pair category and its tensor identification pins the tensor Frobenius,
including the carrier equality; `commonIso` lands in `WeilDQbar` itself. Properness
occurs only in the ordinary-direct-image comparison. The record changes only `lean`
and its signature is copied directly from the existing source. No module was written
because the unchanged node and its same-as interface already have the same content.
