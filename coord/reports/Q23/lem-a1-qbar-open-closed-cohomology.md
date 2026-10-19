## Worker report

Item: lem-a1-qbar-open-closed-cohomology. Group: Q23. Stage 2, 2026-10-18.

The module `Sheaf.Paper.A1QbarOpenClosedCohomology` states
`AlgebraicGeometry.Scheme.A1Cohomology.qbar_open_closed_cohomology`.
Its only postponed proof is this named theorem; its docstring carries all eleven
DAG proof steps and their dependencies. The three local instance aliases cache existing coefficient torsion-freeness,
pair shift additivity and zero-object instances to keep elaboration below the
per-file limit; their attributes do not escape the module. Four public
reducible aliases (`stageCategory`, `stagePreadditive`, `pairPreadditive`,
`pairShift`) also cache the exact already selected category, addition, and
shift instances. They have the identical underlying data and are listed in
`lean.declarations`; there is no new category, addition, or shift choice. Unused generated
size functions and constructor-injectivity lemmas for the assertion records
are disabled, as in the existing comparison-record modules.
The aisle, heart, truncation and zeroth-cohomology aliases likewise reuse the
exact existing operations and their original maps; they avoid repeated
categorical-instance synthesis in the assertion records.
The other declarations are real
abbreviations, constructions, or records packaging the assertion. They do not
replace the PBC categories, the coefficient categories, or the derived operations.
There is no statement correction and no disputed statement.

Hypothesis correspondence:

* The explicitly bound `k : Type u`, `[Field k]`, `[PerfectField k]` express a
  perfect field. `l : ℕ`, `[Fact l.Prime]`, `[Fact (IsUnit (l : k))]` express the
  prime and its invertibility in k. These are not characteristic-positive
  hypotheses: characteristic zero is included.
* `Ω : Type w`, its field and `Algebra ℚ_[l] Ω` instances, and
  `[IsAlgClosure ℚ_[l] Ω]` give the specified algebraic closure. Its universe w
  is independent of u.
* `C U Z : PerAdic.Base k` use the recorded bundle of separated finite-type
  k-schemes, with its actual structure morphism to `Spec (.of k)`.
  `[Smooth (C.scheme ↘ Spec (.of k))]` and `hPure` impose smoothness and pure
  dimension one on C. No smoothness or positive-dimensional assumption is
  imposed on its closed subschemes.
* The displayed j and i, their open/closed immersion instances, `dense`,
  `[IsReduced Z.scheme]`, and `complement` say dense open and reduced closed
  complement, with the actual maps. `IsOver` says these are the induced
  k-morphisms. `Set.range i = (Set.range j)ᶜ` fixes the whole closed support.
* The quantifiers over `T`, `a`, and `IsImmersion a` cover every locally closed
  subscheme in the statement. A separate C clause includes C itself directly.
  T carries only the separated finite-type bundle; these properties are
  automatic for the locally closed subschemes here.

Conclusion correspondence:

* The geometric category throughout is exactly `pbcQbarCategory l Ω T.scheme`.
  `standard` is `PerAdic.commonT`, and `StandardAssertions` identifies it with
  the recorded `pbcQbarStandardT`. Boundedness is `bounded = ⊤`. `Heart` is its
  full heart; `cohomology` is its heart-valued H^0 after shift by m. The natural
  isomorphisms in `StandardAssertions` identify its underlying object with the
  recorded `pbcQbarCohomology`; there is no change of cohomological convention.
* `StandardAssertions` characterizes heart objects by a finite coefficient
  stage and by `PerAdic.LisseStrata` on a finite locally closed stratification.
  That recorded notion is pro-etale locally finite free in degree zero, with
  the existing finite coefficient ring and completed pullback. This is the
  lisse/constructible condition, not an unexplained new heart predicate.
* Its rational assertions and scalar/inclusion comparison clauses give
  ordinary integral-representative cohomology, finite scalar extension and
  common-stage truncations. The continuous-module clause is explicit too:
  `ContinuousStage` has the sheaf localization of the actual completed ring
  at l, specified by invertibility and its ring-sheaf universal property.
  Inverting l agrees with inverting a uniformizer. Its realization is
  normalized by the actual `pbcDerivedExtend` on integral objects and all
  integral maps; preservation of inverses then fixes the fraction maps.
  Its cohomology comparison uses the ambient `DerivedCategory.homologyFunctor`.
  `ContinuousCoefficients` fixes every transition by the completed coefficient
  inclusion. `ContinuousRealization` specifies the filtered colimit by an
  actual universal cocone. Its Qbar realization is actual derived extension
  to that colimit ring; `Cohomology` specifies the natural comparison with ordinary
  cohomology of these continuous Omega-module representatives. Its `extension`
  records exact scalar extension and the comparison with termwise extension,
  normalized by `pbcExtensionCounit`. Its `comparison` definition constructs the normalized
  comparison from `ContinuousStage.cohomology` and the cocone extension. All rings and
  maps are normalized by universal properties, rather than arbitrary choices.
* Scheme-isomorphism invariance is the theorem's third clause: `Restriction`
  preserves both `le n` and `ge n` for every integer n, has the induced heart
  restriction, and cohomology/truncation comparisons. The displayed
  `truncLE_unit` and `truncGE_unit` equations preserve the canonical maps.
  `cohomology_normalized` fixes the cohomology comparison by these truncation
  comparisons and the shift comparison.
* `OpenClosed.openRestriction` and `closedRestriction` give t-exact j* and i*;
  `jointly_detect_zero` is precisely the two restrictions detecting a zero
  sheaf. `pull` is the recorded common-stage completed rational pullback.
* `DirectImage` has actual integral derived pushforward, the recorded raw
  rational functor at each finite field, and `PbcDirectImageBetaSpec` fixing
  its canonical scalar comparisons, including identity extensions. Its
  induced functor uses `StageSystem.Morphism.functor` on the existing pair
  category. `onHeart` is H^0 of this actual derived operation on sheaves.
* `closed_exact` expresses preservation of finite limits and colimits on the
  abelian hearts; `closed_fully_faithful` gives Full and Faithful.
  `closed_counit` makes the actual counit i*i* → id invertible.
  `closed_essential_image` says exactly that j* vanishes.
* `openSheafAdjunction` is j* left adjoint to j* on the hearts, and
  `open_counit` makes the actual counit j*j* → id invertible. Its codomain is
  the constructible heart, so in particular the direct image of a lisse sheaf
  is constructible. The derived and ordinary adjunctions are connected by
  `UnitNormalization` and `HeartAdjunctionNormalization`; they are not
  arbitrary adjunction structures on unrelated functors.
* `lower_bound` says Rj preserves D≥m for every m. In this bounded standard
  structure that is exactly H^a = 0 for a < m. `bottom` is the displayed
  isomorphism H^m(Rj M) ≅ j* H^m(M). `bottom_natural` retains naturality in M,
  and `bottom_counit` fixes its transpose as cohomology of the actual derived
  counit, so a scalar-twisted bottom comparison is not substituted.
* `unit_in_degree` is the equality between cohomology of the actual derived
  unit, followed by the bottom and restriction identifications, and the
  ordinary sheaf adjunction unit. Its ONLY bound is on `(pull j).obj K`.
  There is no assumption that K itself lies in D≥m.
* `AutomorphismCompatibility` spells out the reindexing isomorphisms and their
  commutative squares. `ExchangeNormalization` fixes derived push reindexing
  by the actual integral `pbcActualCompletedExchange`, before scalar descent.
  `AdjunctionCommutes` retains both unit and counit squares, for both ordinary
  and derived adjunctions. The cohomology and bottom equations are also
  displayed. Applying this naturality to the recorded Cartesian geometric
  Frobenius squares gives the finite-field clause. `Commutes` is exactly the
  natural-transformation morphism equation in an endofunctor-fixed pair category, as used by
  `sfWeilComplex`/`sfWeilSheaf`; `pairTransformation` uses the existing `IsoAlgebra.mapOfNatIsoHom` to
  construct the actual transformations on those fixed-pair categories; no
  triangulation of that category is assumed
  or asserted. Truncation maps commute by the normalized restriction
  comparisons. Naturality is packaged for isomorphism squares, so it applies
  directly to the specified Frobenius isomorphisms.

Recorded dependency declarations read and used:

* `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory` and its existing stage system.
* `Sheaf.Paper.LisseIntegralSmallCoefficients`: the recorded small-coefficient
  lisse notion, via the imported LisseAdicSheaves interface.
* `Sheaf.Paper.PbcQbarStandardCohomology`: `pbcQbarStandardT`,
  `pbcQbarCohomology`; its ordinary integral/rational cohomology imports stay.
* `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`, Heart and truncation
  modules: `TStructure`, its heart, le/ge and canonical truncation arrows.
* `Sheaf.Paper.SfWeilSheafComplex`: `WeilConjectures.sfWeilComplex`,
  `sfCommonStageWeilComplex`, `sfWeilSheaf`, and the fixed-pair convention.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
  Finite type uses `LocallyOfFiniteType` and `QuasiCompact` in `PerAdic.Base`.
* `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
* Mathlib OpenImmersion and ClosedImmersion: `IsOpenImmersion`,
  `IsClosedImmersion`; `IsReduced` uses the actual scheme property.
* `Sheaf.Paper.AdicHeartIntrinsicFibres` (and AdicHeartPullbackFibres):
  `PerAdic.Base`, `commonT`, `commonPull`, `rationalT`, `rationalLE`,
  `rationalGE`, `rationalCohomology`, `RationalStandardAssertions`,
  `LisseStrata`, and `pullInclusionIso`. The last is reused directly rather
  than reconstructing its opaque pull-family interface.
* `Sheaf.Paper.PbcDescentFunctors`: `pbcDescentDirectImage`,
  `PbcDirectImageBetaSpec`; actual completed push/pull and derived adjunction
  come through its recorded dependencies. `StageSystem.Morphism` supplies
  the real descent functor, composition and transformations.
* `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`:
  `homology₀`, `homology₀ε`, and the existing abelian heart instance.
* All available proof-dependency modules are retained as regular imports,
  including bottom-unit normalization, bounded-below derived adjunction,
  negative vanishing, integral constructible finiteness, ringed open/closed,
  module adjunction, sectionwise isomorphism restriction, site localization,
  and K-injective resolutions. The current main now records both realization lemmas. Their modules
  `ContinuousRationalDerivedRealization` and `RationalDirectImageRealization`,
  as well as `CompletedCondensedCoefficients`, are retained as ordinary proof
  imports. The present module supplies its needed canonical comparison
  assertion without assuming those lemmas as extra hypotheses.

Edge cases checked before finalizing the signature:

* Empty C is allowed when the recorded pure-dimension predicate is vacuous;
  all categories and complement conditions remain meaningful. There is no
  hidden nonemptiness hypothesis on C or its strata.
* j = identity and Z empty; U empty when C empty; zero sheaves and complexes.
  In these cases the actual adjunction and support formulas specialize
  correctly. Repeated coefficient fields are included in beta normalization.
* Arbitrary positive, zero and negative m. A K with cohomology supported on Z
  below m is allowed: only j*K has the bound in `unit_in_degree`.
* Disconnected U and nonconstant finite ranks on strata are allowed.
* Characteristic zero, and coefficient universes independent of scheme size.
  The universal cocone avoids imposing an extra equality of universes.

Searches (also logged in searches.jsonl):

* msearch leanfinder: “Bounded constructible l-adic cohomology open closed
  restriction t exact and bottom direct image unit”: eight unrelated matches,
  including Profinite exactness and scheme restriction; no exact statement.
* msearch loogle: `CategoryTheory.Triangulated.TStructure, CategoryTheory.Adjunction`:
  no hits.
* msearch grep: `open.closed|OpenClosed|constructible` in
  `CategoryTheory/Triangulated`: no hits.
* msearch leansearch: “Bounded constructible l adic sheaves open closed immersion
  cohomology t structure”: eight SheafedSpace/LocallyRingedSpace immersion
  matches; none gives this statement.
* rg in the named upstream WeilConjectures and side Sheaf directories for
  open/closed constructible cohomology, standard hearts and rational
  realization; grep of the exact item id in upstream: no exact theorem.
  The searches found and reused the existing standard cohomology, adic-heart,
  rational descent, actual exchange and pull-inclusion comparison interfaces.
* Read the current blueprint proof, Steps 1 and 3 and its Weil-pair convention,
  and BS Lemmas 6.7.2/6.7.11, Definitions 6.8.3/6.8.6/6.8.8,
  Lemma 6.8.7 and Remark 6.8.15 in the supplied PDF.

## Repair of independent return eac07718d954

The initial saved-packet dry run succeeded at ba2c46fe30. The subsequent
mathematical self-check confirmed that the saved module still had the two
returned defects, so it was not re-pushed unchanged.

**H3 repaired.** `ContinuousRealization.Cohomology` is now a structure of
specified exact-extension data, with its normalized comparison constructed
by `ContinuousRealization.Cohomology.comparison`. The theorem chooses `R` and `H : R.Cohomology`
once, before its other conclusions, and the automorphism record takes those
same `R` and `H` as parameters. Its `continuousCohomology` field does not
quantify over arbitrary realizations or comparison isomorphisms.
`ContinuousCohomologyFrobenius.equivariant` refers only to
`H.comparison l Ω E n`. Thus the return's disconnected-curve example, with
an automorphism swapping components and a non-invariant componentwise unit,
no longer forces a scalar-twisted comparison to be equivariant. This changes
the formal packaging to the canonical comparison meant by the unchanged node.

**F2 repaired.** `H.comparison` constructs the comparison as the composite of
`ContinuousStage.cohomology n`, extension along `R.cocone.ι.app E`, and the
canonical cohomology/exact-extension comparison.
`ContinuousExactExtension.normalized` fixes its derived-to-termwise comparison
by the actual `pbcExtensionCounit`, ruling out scalar twists at that step.
`exactCohomologyExchange` uses the existing
`Functor.mapDerivedCategorySingleFunctor` and
`Functor.mapDerivedCategoryHomologyFunctorIso` constructions.
`CohomologyRestriction` packages t-exact triangulated restriction, and its
`cohomology` definition uses the existing canonical `Functor.eTruncLTIso`
and `Functor.eTruncGEIso` followed by the shift comparison.
`RationalCohomologyRestriction` specializes this data to the exact recorded
finite-stage standard structure and its original shift instance. Thus the
truncation arrows are canonical constructions, not new freely chosen maps.
`ContinuousFrobeniusTransport.leftExchange` is constructed from this
restriction comparison and `exchange`; `rightExchange` is constructed from
`exchange` and `exactCohomologyExchange` for the actual
`proEtaleRingModulePullback`. They are definitions, not free fields.
The module pullback and fixed-pair transport are also definitions of the real
operations, rather than fields constrained only later by equalities.

The additional helper records are parts of this item's comparison assertion,
listed in `lean.declarations`, with source and blueprint docstrings. They
introduce no new independent mathematical notion or postponed theorem.
No DAG prose statement, statement dependencies, proof, or proof dependencies
are changed. The sandbox node was compared with the current shared node;
only its `lean` record differs.

## Second reading by Q23

I reread the unchanged node and the repaired assertion, using the returned
counterexample as an additional edge case. The theorem binders still express
a perfect field, an invertible prime, and an algebraic closure independently
sized from the schemes. `PerAdic.Base` provides separated finite type, and
the displayed smoothness and pure-dimension-one conditions concern only C.
The open/closed immersion, over-base, dense-range, reducedness and exact
complement hypotheses are unchanged. Empty schemes, disconnected schemes,
characteristic zero, and identity immersions remain included.

The selected `R` and `H` give the node's agreement with ordinary continuous
module cohomology, with the finite-field comparison and cocone extension now
explicitly fixing that agreement. `StandardAssertions` gives the bounded
standard t-structure, the finite locally closed lisse-stratification heart,
finite scalar compatibility and common-stage truncations. The quantified
locally closed `T` clause supplies the same assertions for every immersion;
the scheme-isomorphism clause supplies normalized t-exact restriction.

The `OpenClosed` fields were preserved: t-exact j* and i*, joint detection of
zero on hearts, actual direct images and normalized adjunctions, exact and
fully faithful closed direct image with its essential image, the open counit,
lower-bound preservation, the natural bottom-cohomology isomorphism fixed by
the derived counit, and the actual-unit equation whose sole lower bound is
on j*K. This still covers any integer m, zero complexes, and objects with
lower cohomology supported on Z.

The last conjunct uses the same selected `R` and `H` for every displayed
automorphism square. Its continuous equivariance equation uses only
`H.comparison l Ω E n`, and both exchanges in that equation are constructed
from the canonical operations described above. Component-swapping
Frobenius automorphisms therefore do not impose equivariance on an arbitrary
componentwise scalar twist. The remaining automorphism fields retain the
normalized direct-image exchanges, derived and heart unit/counit squares,
restriction cohomology equations and bottom-cohomology equation. This gives
the node's Frobenius clause in the recorded fixed-pair categories without
asserting a triangulation of those categories.

The only `sorry` is the item's named theorem, with the complete eleven-step
proof plan. All new constructions contain real data or package asserted
properties in the theorem's conclusion. There is no statement dispute or
source-based node correction.

Additional repair searches: `rg` in Mathlib and the upstream exact-functor
modules found `mapDerivedCategoryHomologyFunctorIso` and
`mapDerivedCategorySingleFunctor`. Reading the published
`TExactTruncationComparison` module located the canonical upstream
`eTruncLTIso`/`eTruncGEIso` constructions, which are reused.
The wrapper search `msearch.py ... grep
"eTruncLTIso|mapDerivedCategoryHomologyFunctorIso" CategoryTheory` returned
no Mathlib hits: these particular comparisons are upstream extensions.

Performance diagnosis after a dry-run timeout: Lean's profiler identified
an expensive `inferInstance` search in the existing coefficient torsion-free
alias. It now applies the exact existing
`DivisionSemiring.to_moduleIsTorsionFree` instance directly. This is a reuse
of Mathlib's field-module instance, with no new theorem or mathematical data.
Further profiling located repeated synthesis of the same stage-category,
preadditive and common-stage shift structures. The four public reducible
instance aliases above reuse those exact instances and avoid repeating that
search. They change no construction or hypothesis.
The profile directives and temporary diagnostic modules are not delivered.

## Validation

The saved packet's initial dry run passed. After the returned mathematical
defects were repaired, `scompile.py` compiled the sandbox and final module
cleanly (59.6 s and 56.2 s), with no non-sorry warnings. The final
`deliver2.py --no-push` gate and delivery are run on this repaired packet. No direct Git commands, source-tree edits,
launcher-script edits, or global builds are used.

## Saved-packet continuation and self-check

The resumed sandbox retained the selected-realization H3 repair. The F2
self-check found that `CohomologyRestriction.cohomology` was still a free
field, contradicting the preceding report's description. It is now a real
definition, composing `Functor.eTruncLTIso`, `Functor.eTruncGEIso` and
`Functor.commShiftIso` with their canonical associators. Its ambient category
has its existing triangulated structure. The actual finite-stage category
supplies this structure without an extra hypothesis on the curve.
`leftExchange` therefore uses the constructed restriction comparison;
`rightExchange` uses the canonical homology/exact-pullback comparison.

The retained `OpenClosedCore`/`OpenClosedAssertions` refactor packages the
same data and propositions formerly held in one record. In particular the
joint detection, exactness, full faithfulness, essential image, counits,
bottom normalization, naturality and degree-unit clauses are conjuncts of
`OpenClosedAssertions`. `OpenClosed` contains the core and all those
assertions. Its operation accessors and `bottom` return the original core
data. Every clause is still required; no proposition was dropped.
All these public helpers are listed in the node's `lean.declarations`.

Self-check of the returned counterexample: for a disconnected curve and
component-swapping automorphism, the equation mentions only the selected
`H.comparison`. It does not quantify over a comparison composed with a
componentwise unit. The exchanges are definitions using the same realization
exchange, so they are not independently selected to force a square.
The unchanged conclusion still imposes the lower bound only on `j*K` in
the degree-unit assertion. The sandbox and current shared node have identical
non-`lean` fields. No source statement correction is needed.

Further performance repair: the specialized rational restriction and its
left-exchange construction now supply the named `pbcScalarRational*`
additive-shift, pretriangulation and Verdier instances explicitly, scoped
inside their definitions with the existing rational shift. Registering
these instances globally was tested and rejected because the common-stage
category uses its independently normalized stage shift. The delivered
construction retains that common-stage choice and uses the rational-stage
adapters only in the definitions that already select that rational shift.

Final resumed-packet validation: `scompile.py` exited successfully. The
sandbox compilation was clean at 54.7 seconds; after a library-path timeout,
the wrapper's required current-server confirmation compiled the final module
cleanly at 58.3 seconds, under the unchanged 60-second limit. There were no
errors or non-sorry warnings. The two accessor applications now explicitly
supply their coefficient arguments. The profiler is confined to a scratch
file and is not delivered. The delivery dry run and push below operate on
this repaired packet.
