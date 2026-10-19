## Worker report

Delivered `Sheaf.Paper.CompactFiberStalk`, namespace
`WeilConjectures.PurityFiniteSetting`. The node is realized by four named theorem
statements, with `sorry` proofs: `compactFiber_finite`, `compactFiber_integral`,
`compactFiber_rational`, and `compactFiber_qbar`. The other four declarations are
real definitions of the two canonical fibre squares, the finite comparison map,
and the proposition spelling out the common-stage formula. No definition contains
`sorry`. The node copy changes only `lean`; no statement correction is requested.

Source read: the current main-20261015 `sk-prop-an/lem-pur-cfiber-stalk.md`, its
containing unit, and the five-step expanded proof in the DAG. In particular Step 1
explicitly reads the displayed stalk/fibre comparison as the compact-support
exchange on Spec Omega, rather than requiring new definitions of stalks or of
compactly supported cohomology. The module follows this reading at all four
coefficient stages. It does not replace the specified arrow by a chosen isomorphism.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed purity conventions are `P : PurityFiniteSetting.{u}`. Its `field`,
  `coefficients`, `extension`, `level`, and `level_pos` are the recorded finite-field
  datum, prime distinct from the characteristic, finite intermediate coefficient
  field in the fixed coefficient closure, and positive finite level. Its `Ring` is
  the actual quotient O_E/(varpi_E^n); `Coefficient` is its standard ULift.
- The scheme called E in the node is called `X`, to distinguish it from the
  coefficient field `P.extension`; B is `Y`. Both have `Over (Spec (.of P.field.k))`
  structures. `hXft`, `hXqc`, `hYft`, `hYqc` express that both are finite type over k.
  This is the global finite-type setting used by the node's proof, not an assumption
  of properness or separatedness of either structure morphism.
- The morphism pi is `f : X ⟶ Y`, with `hfOver : f.IsOver (Spec (.of P.field.k))`.
  `hfSep : IsSeparated f`, `hfft : LocallyOfFiniteType f`, and
  `hfqc : QuasiCompact f` express precisely separated finite type. All eight named
  hypotheses are retained with `include ... in` on each theorem. Compiler `#check`
  inspection confirmed that all occur in every elaborated theorem signature;
  those diagnostic commands were removed from the delivered file.
- At finite coefficients the input is
  `finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos X`.
  This is the existing intrinsic bounded constructible finite-Tor category, not an
  arbitrary complex and not an input with an added etale-origin witness.
- At integral coefficients the input is
  `finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X`, with
  the existing completeness, common cohomological bound, and uniform Tor bound.
  `integralDetailedTransport X ...` is the published coefficient-ring identification
  on its actual underlying object. `hc` is a conclusion giving the proof needed by
  the existing exchange API, not a new input hypothesis.
- At rational coefficients the input is the existing
  `sfRationalConstructibleCategory P.coefficients.l P.extension X`. This is D^b_ctf
  because at field coefficients the recorded finite-Tor definition is D^b_c.
  `K.obj.obj` is its unchanged integral representative. The arrow is the image of
  the specified completed exchange under `ScalarLocalization.localization` at the
  actual lifted uniformizer. We use the ambient localization only to expose this
  concrete arrow without adding endpoint membership assumptions: Hom between
  constructible objects is already the same full-subcategory Hom, and tensoring it
  with the fraction field is precisely the recorded rational Hom construction.
- The Qbar clause uses `P.coefficients.Qbar` and the existing `pbcQbarCategory`.
  This is the raw pair-category presentation identified with the chapter's category
  in Step 4 of this node's proof. `CompactFiberQbarFormula` constructs the dimension,
  invertibility, and Noetherian instances from the fixed finite-type setting using
  published theorems. They are never extra hypotheses. Its `Nonempty` asserts
  existence of the published normalized exchange model. For every such model and
  every common-stage object, its actual descended comparison component is an
  isomorphism. `CbcQbarExchangeModel` retains the prescribed completed-unit and scalar
  mate equations; the maps or coefficient compatibilities are not arbitrary data.
- The geometric point is `Omega : Type u`, `[Field Omega]`, `[IsAlgClosed Omega]`,
  `s : Spec (.of Omega) ⟶ Y`. Its image need not be a closed point and its field
  need not equal k or an algebraic closure of k. The map to Spec k is the composite
  `s ≫ (Y ↘ Spec (.of P.field.k))`; no independently specified field embedding is
  imposed. These are the geometric-point convention collected by
  `def-weil-scheme-morphism-properties`.
- The fibre is literally `pullback f s`. The pullback square is
  `IsPullback.of_hasPullback f s`; its structural map is `pullback.snd f s`, and
  restriction of the input is along `pullback.fst f s`. `c.baseChange s` is the
  recorded base change of a compactification. The proper/open square helpers use
  its actual projection and universal pullback identifications, with real data.
- `(Rf! K)_s` is read as geometric-point pullback of the compact-support direct
  image, and `RGamma_c(X_s,K|X_s)` as compact support along the fibre projection,
  in the derived coefficient category on Spec Omega. This is exactly the endpoint
  reading fixed by proof Step 1. At finite level the identity pointed neighbourhood
  computes the etale stalk on the etale-origin witness. The intrinsic coefficient
  realization is only a canonical change of coordinates. Integral and field
  stages use their specified completed and scalar-localized point pullbacks.
- The comparison at finite level is the component of
  `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`, on the image
  under the inverse of `sfIntrinsicDerivedEquivalence`. Its formula is the actual
  derived proper mate followed by the inverse open base-change comparison.
  At integral level it is `completedCompactSupportExchange`; the two squares are
  the explicit canonical proper/open squares above. At rational level it is actual
  functorial localization of that arrow; at Qbar level it is
  `(StageSystem.Morphism.descNatTrans D.exchange).app K` for the prescribed model.
  `IsIso` in each clause is the isomorphism assertion in the display.
- Quantification over compactifications and generating tuples exposes presentation
  parameters of the existing operations. It imposes no compactification-existence
  or completeness hypothesis: a separated finite-type morphism between the given
  finite-type k-schemes has a compactification, by the imported Nagata interface.
  The tuple condition is only equality with the already fixed uniformizer ideal;
  all such presentations give the comparison asserted in the node. No existential
  choice is used to manufacture the comparison arrow.

Dependency declarations used directly (other stated proof dependencies are imported
privately, as required by the stage rule):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, `.coefficientPrime_isUnit_stalk`.
- `def-weil-scheme-morphism-properties` is an umbrella with no independent notion,
  no `lean` record and no Mathlib match. Its actual notions are the existing
  `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `Scheme.Over`, `Scheme.Hom.IsOver`, and scheme morphisms from Spec of an
  algebraically closed field. I read their Mathlib signatures/docstrings; no
  substitute umbrella definition is needed.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructibleCategory`,
  `.finiteTorConstructibleIntegralCategory`, and the field-stage convention.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.baseChange`,
  `.isPullback_i_ofIsPullback`, with its actual `.isoPullback` and projection laws.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `Scheme.sfIntrinsicDerivedEquivalence`; this is the exact canonical realization,
  including its specified section-normalized direct-image comparisons.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`:
  `ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`. Its complete
  current source was obtained with `scompile.py --source`, since it is absent in
  the older local upstream checkout and the listed side framework.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `Scheme.completedCompactSupportExchange` and the published `cbcCompleteProperty`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `Scheme.integralDetailedTransport`, using its projection-normalized coefficient
  comparison. `BoundedConstructibleComplete` supplies `pbcIntegralDatum`,
  `PbcIntegralRing`, `pbcUniformizer`, `PbcCompletedDerived`.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleCategory`;
  `Sheaf.CategoryTheory.ScalarLocalization`: the existing `localization` functor.
- `Sheaf.Paper.QbarCompactSupportBaseChange`:
  `Scheme.CbcQbarExchangeModel`; `PbcQbarCategory` supplies `pbcQbarCategory`;
  `StageSystem.Morphism.descNatTrans` is the existing common-stage descent map.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.exists_topologicalKrullDim_le`; and
  `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`. The latter is the already
  available one-line packaging of the Mathlib match for the Noetherian proof node.

Edge cases checked before finalization:

- `X` empty or the fibre empty: both comparison endpoints are zero. No inhabitedness
  or surjectivity assumption excludes them.
- `Y` empty: there is no geometric point `s`, so the geometric-point quantifier has
  exactly the intended empty domain.
- Zero input at every coefficient stage: all operations are additive and give zero.
- `f = id` and `Y = Spec Omega`, `s = id`: the identity square and its specified
  compactification give the identity comparison; no nontriviality hypothesis occurs.
- Positive level 1 and ramified coefficients are included. Level 0 is excluded by
  the source's `n ≥ 1`. There is no Kummer-level divisibility restriction.
- Arbitrary geometric fields and nonclosed images are included. The small site's
  object universe remains u+1 and its morphism universe u; coefficients are lifted
  canonically and no equality between site object/morphism universes is imposed.
- Integral generating tuples have arbitrary length, including zero if its span is
  the ideal. `hc` is proof-only, hence its choice cannot alter the arrow's data.
- Rational objects and all common-stage Qbar pairs are included, including equal
  coefficient fields and changes of representative. The Qbar model is exactly the
  normalized published model, not a free natural transformation.

Searches for an exact existing statement (all run with the authorized msearch
wrapper, group N1/item lem-pur-cfiber-stalk):

1. LeanFinder, `stalk of compactly supported direct image at a geometric point is
   compactly supported cohomology of geometric fiber`: 8 hits, headed by
   `TopCat.Presheaf.stalkSpecializes_stalkPushforward_apply` and
   `TopCat.Presheaf.stalkPushforward_germ_apply`; no compact-support fibre formula.
2. Loogle, `CategoryTheory.GrothendieckTopology.Point.sheafFiber`: 12 hits for the
   general fibre functor, its exactness/adjoint/compatibility declarations; no match.
3. Mathlib grep, `compactSupport.*[Ss]talk|[Ss]talk.*compactSupport|cfiber` under
   AlgebraicGeometry: wrapper returned only `Scheme.Etale.geometricFiber`, not a
   compact-support theorem.
4. LeanSearch, `stalk compact support cohomology geometric fiber derived direct
   image`: 8 hits, including `TopCat.Presheaf.stalk` and
   `Scheme.Modules.restrictStalkNatIso`; no match.
5. `rg` under Mathlib AlgebraicGeometry, upstream WeilConjectures, side
   `lean/Sheaf`, side framework, and `dag/lean_names_upstream.json`, for `cfiber`,
   compact-support/stalk combinations, and all proposed declaration names: no
   declaration already states this node. The upstream general compact-support
   exchange and base-change theorem were found and reused, not restated.
6. The exact blueprint-id search in upstream WeilConjectures returned no hit.

Validation: final module compiled by `scompile.py N1 lem-pur-cfiber-stalk` both as
sandbox and library module, with no errors or warnings (5.2 s and 8.0 s respectively
in the last run). Both use the default 60-second limit. The only postponed proofs
are the four named coefficient clauses of this node. All other definitions have
real data. No `STATEMENT-DISPUTED` issue remains.

## Worker self-check

I reread the node against all four statements, checked the retained elaborated
hypotheses with temporary `#check` commands, checked all lines are at most 100
characters, and verified that the JSON differs from the base only in `lean`.
The dispatcher explicitly prohibits starting other agents; this is a worker
self-check, not a claim of an independent second reading. The requested independent
review is the maintainer's review of this delivery.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
