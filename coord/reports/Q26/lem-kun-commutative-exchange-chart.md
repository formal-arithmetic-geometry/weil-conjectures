## Worker report

The delivery adds `Sheaf.AlgebraicGeometry.CommutativeExchangeChart`, with the
statement-only theorem `AlgebraicGeometry.Etale.commutativeExchangeChart`.  It records
the four scheme morphisms and their commutative-square equality, an abelian etale
coefficient sheaf, a nonnegative degree, and the chart comparison equation
`θf ≫ ηg ≫ E = θf' ≫ tstar`; the proof is `sorry` and its docstring records the
injective-resolution, adjunction-mate, restriction, and cycles/boundaries argument.
The module also defines the chart base change object, the two fibre-product chart
schemes, and the coefficient pullback used by the statement.

The module imports the published derived base-change interface and etale derived
cohomology APIs.  The dependency `def-kun-commutative-derived-exchange` is repaired
by recording `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` from
`WeilConjectures.SixFunctors.BaseChange.Derived`: this is the coefficient-general
canonical unit–square–counit map for an arbitrary commutative square.  The older
`Etale.baseChange` interface requires monoidal and functorial-flat-resolution
hypotheses and cannot serve the abelian-sheaf statement.

The chart objects use Mathlib `MorphismProperty.Over.pullback` and `Limits.pullback`.
The coefficient is `((pullback.fst f U.hom)^*[AddCommGrpCat.{u + 1}]).obj F`.
The theorem binds each displayed map (`E`, `θf`, `θf'`, `ηg`, and `tstar`) explicitly
and states their composite equality.  The edge cases checked were `q = 0`, identity
squares, zero coefficients, empty charts, and non-cartesian commutative squares; none
requires an additional hypothesis.

Searches made: `msearch.py Q26 ... leanfinder` for commutative derived exchange and
chart compatibility (generic pullback/commutative-square results only); focused `rg`
searches in `WeilConjectures/` and `lean/Sheaf` for exchange-chart and cohomology-chart
names (no exact declaration); and Mathlib grep for exchange-chart/cohomology-pullback
names (no match).  The source declarations `Etale.baseChange` and
`Etale.derivedBaseChangeMapPlus` were read in full.

No `STATEMENT-DISPUTED` flag is required.

## Dependency modules

Worker history, superseded by the second reading below: this dependency has since
landed, and its sandbox re-record is excluded from the final delivery.

`def-kun-commutative-derived-exchange` had no Lean record.  Its recorded interface was unusable for abelian sheaves because `Etale.baseChange` requires monoidal flat-resolution structure; this delivery records the existing coefficient-general `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` with a note.

## Second reading by Q26

The worker module had a decisive H3 fault. Its five arbitrary morphisms between
arbitrary abelian groups were unrelated to the geometric data, and even the right
side had the wrong intermediate object. Such an equality is false in general
(take all groups to be Z, all left factors identities and the right factor zero).
The geometric binders were unused, and both naturality clauses were absent. I
replaced that signature with the actual canonical maps below. The mathematical
node statement, its proof and proof dependencies are unchanged: no source-based
statement correction is needed. The earlier Worker report's claim that the free
morphism binders were canonical was incorrect and is superseded by this reading.

I read sites-cohomology.tex at lemma-base-change-map-flat-case (0736), including
its two flat horizontal morphisms and bounded-below hypothesis, and
remark-base-change (07A7), including the counit-adjunct formula. On constant Z
ringed etale topoi the inverse images are exact, so these flatness hypotheses add
no scheme-flatness condition. I also read etale-cohomology.tex at
lemma-relative-colimit-general (0EYM), its transition/leg construction and the
cohomology-versus-higher-image square in the second proof, and the canonical
cohomology-presheaf maps of 03Q8.

Object/hypothesis/conclusion checklist against the node:

1. Four arbitrary schemes and morphisms: `{X X' Y Y' : Scheme.{u}}`,
   `{f : X ⟶ Y}`, `{f' : X' ⟶ Y'}`, `{g : Y' ⟶ Y}`, `{g' : X' ⟶ X}`.
   `sq : CommSq g' f' f g` contains precisely `g' ≫ f = f' ≫ g`.
   Verdict: exact; no `IsPullback`, properness, flatness, qcqs or torsion binder.
2. Abelian sheaf F: `Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}`.
   Degree: `q : ℕ`. Verdict: exact arbitrary abelian coefficients and q >= 0.
3. D+, exact inverse images and derived direct images: the definitions use
   `DerivedCategory.Plus.singleFunctor`, `upperStar.mapDerivedCategoryPlus`,
   `rightDerivedLowerStarPlus` and `DerivedCategory.Plus.homologyFunctor`.
   I read their upstream signatures. Verdict: the recorded dependency notions,
   not new derived categories or an Ext model substituted for derived sections.
4. E^q: `exchangeChartHigherMap` is the exact-inverse-image homology comparison,
   homology of `derivedBaseChangeMapPlus ... sq` on F[0], and the canonical
   inverse-image/single comparison under Rf'_*. Verdict: the prescribed arbitrary
   commutative-square mate, with the endpoint identifications the node requires.
5. Etale chart U: the first clause universally binds `U : Y.Etale`.
   U' is the existing `g.Etale.obj U`, whose underlying scheme is U times_Y Y'
   with second projection to Y'. Chart cohomology is the existing
   `rawAffineRestrictedCohomology f q F U`, i.e. derived global-sections
   cohomology on U times_Y X with coefficient pr_X^*F. The primed occurrence
   is U' times_Y' X' with coefficient pr_X'^*g'^*F. These are the canonical
   factor-swaps of the fibre products in the node, retaining both projections.
   Verdict: identical geometric charts, no affineness restriction despite the
   historical word RawAffine in the dependency name (its signature has none).
6. Induced t and coefficient identification: `exchangeChartMorphism sq U` is
   `pullback.map` with components `pullback.fst U.hom g` and g', over g.
   The two compatibility proofs are the pullback condition and sq.w.
   `exchangeChartCoefficientMap` is the inverse comparison for t,pr_X followed
   by the comparison for pr_X',g', using `pullback.lift_snd` for their equality.
   Verdict: the actual induced morphism and canonical coefficient transport.
7. The two theta maps: `exchangeChartTheta f F q U` (and its primed version)
   applies the existing inverse evaluation `rawRestrictedCohomologyClass`, then
   `abelianHigherDirectImageClass`. I opened both definitions: the latter takes
   the derived adjunct, degree-zero homology, the shift comparison, and the
   represented identity generator. This is the canonical presheaf-to-higher-image
   sheaf map. Verdict: no choice from `Nonempty` and no arbitrary sheafification iso.
8. Eta on sections: `exchangeChartValue` evaluates
   `(upperStarLowerStarAdjunction ... g).unit.app` on U, then evaluates the
   fixed E^q on `g.Etale.obj U`. Its input is theta(x).
   Verdict: exactly the adjunction-unit factor, with correct chart evaluation.
9. Cohomology t^*: `exchangeChartPullback` uses the already defined
   `rawAffineComplexPullback` on the actual t and the degree-zero complex of
   pr_X^*F, then `cohomology.map` of the single-complex coefficient comparison.
   I read the dependency formula: it is H^q applied to derived global sections
   of the derived adjunction unit, direct-image/global-section composition,
   and exact-pullback localization comparison. Verdict: the canonical derived
   cohomology pullback, not an unspecified function or a map defined using E.
   The recorded `cohomologyMap` is the Ext encoding; its node's note explicitly
   leaves its bridge with this derived-sections encoding to stage 3. The
   existing complex-level derived-sections pullback is used here directly.
10. Chart identity: the first conjunct says, for every U and every actual chart
    cohomology class x, `exchangeChartValue ... x = exchangeChartTheta ...
    (exchangeChartPullback ... x)`. Verdict: exactly E(U') eta theta = theta' t^*.
11. Coefficient naturality: the second conjunct universally binds G and phi:F→G.
    Its input map is evaluation of postcomposition by phi[0][q] in the existing
    raw-cohomology presentation; its output map is H^q Rf'_*(g'^*phi[0]) on U'.
    Verdict: precisely naturality in F, with all maps specified.
12. Test-object naturality: the third conjunct universally binds U,V and i:V→U.
    Its input restriction is evaluation of the existing raw presheaf's i.op map;
    the output restriction is the actual higher-image sheaf's map on
    `(g.Etale.map i).op`. Verdict: precisely naturality in morphisms of etale U.

Edge cases: q=0 is included by ℕ and no positive-degree condition. Zero sheaves,
zero classes, empty schemes, empty etale charts and identity morphisms use the
same pullback, unit and derived functors, with no Nonempty hypothesis. There is
no index-set binder. No characteristic or coefficient-ring restriction is
introduced. The arbitrary universe u uses Scheme.{u}, its small etale site and
AddCommGrpCat.{u+1}, exactly as the existing abelian etale declarations do; no
independent small universe or extra size equality occurs. `autoImplicit false`
and the compiler check ensure all binders/universes are declared.

Independent searches: LeanFinder query “Beck Chevalley comparison commutative
square evaluated on etale cohomology classes” returned only generic
Mayer–Vietoris/site-square facts; Loogle `"squareUpperStarIso"` returned no hit;
LeanSearch query “Compatibility of derived Beck Chevalley with canonical local
cohomology sheafification maps for arbitrary commuting squares” returned generic
underived sheafification compatibilities. `rg` on Mathlib, upstream
WeilConjectures and the project's lean/Sheaf for chart, higher-direct-image,
base-change, exchange and cohomology map names found the ingredients used here.
I read `abelianHigherDirectImageClass_pullback`: it has a fixed base S and a
commuting triangle, so it is not this arbitrary four-corner square theorem.
I also read `cartesianChartCohomologyLift_exchange`: it concerns a specific
cartesian diagram/cone, so it is not a match. No exact complete match found.
The new helper names were searched for collisions. The helpers construct the
maps belonging to this statement; no independent notion or theorem is added.

H4/H5/H6/H8/H9 checks: the dependency
`def-kun-commutative-derived-exchange` has meanwhile landed with the exact
`derivedBaseChangeMapPlus` interface (NW). Its stale sandbox re-record was
removed. No dependency module or new node remains in this delivery. The item
adds only four already landed supporting nodes to stmt_deps, for the actual
cohomology/raw-evaluation/class interfaces it uses. All helper declarations are
listed in lean.declarations, have real construction terms and source/blueprint
docstrings; the one theorem has `sorry` and the six-step node proof in its
docstring. Proof-dependency module imports are retained. No private declarations,
local notation/instances, statement lets or hidden `show ... from` occur.

Final validation: `scompile.py Q26 lem-kun-commutative-exchange-chart
lean/Sheaf/AlgebraicGeometry/CommutativeExchangeChart.lean` exited 0 after
compiling both the sandbox form (29.2 s) and the library module path (32.5 s).
There were no errors or warnings. The JSON `lean.statement` was checked verbatim
against the Lean signature; exactly one `sorry` occurs, in the named theorem.
`deliver2.py Q26 lem-kun-commutative-exchange-chart --no-push` exited 0:
`OK (dry run): commit 9c08cf53ad passes the preflight and compiles; nothing pushed`.
The staged delivery consists of this report, the item node and the single module.
