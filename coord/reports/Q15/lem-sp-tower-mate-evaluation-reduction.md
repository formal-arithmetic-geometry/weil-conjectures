## Worker report

Item: lem-sp-tower-mate-evaluation-reduction. Group Q15, stage 2.

The module `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` states
`AlgebraicGeometry.ProEtale.SpTowerMate.tower_mate_evaluation_reduction`.
This is the only theorem and the only `sorry` in the delivery. Every helper has
real data. The node is unchanged outside `lean`; there is no statement correction,
new definition node, or dependency repair.

I read the item and every statement dependency, their recorded modules and
signatures/docstrings. The retired CompactObject example is empty in this
checkout; I also read its current recorded upstream owner
`WeilConjectures.CategoryTheory.CompactObject` for the actual conventions.
The source read was the current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-tower.proof.md`,
paragraphs (1) and (2), together with the item's six proof steps.

### Hypotheses and objects

- The global finite-field datum is the binder
  `k : WeilConjectures.FiniteFieldDatum.{u}`. Its fields give the finite field
  and its chosen algebraic closure. The coefficient prime is `(l : ℕ)
  [Fact l.Prime]`, with `_hne : l ≠ k.p`. The field extension is `(E : Type u)
  [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
- The actual coefficient rings are `SpTowerShriek.R l E n`, hence
  `Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n+1)`.
  Index zero is the paper's first positive level. `SpTowerCalculus.quotient`
  is the actual quotient homomorphism for `h : m ≤ n`. This retains ramified
  extensions; no uniformizer-power quotient is substituted silently.
- `X Y X' Y' : Over (Spec (CommRingCat.of k.k))` and, for each of the four
  structure morphisms, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  express exactly the standing scheme setting. All four square maps are
  morphisms in this Over category, so they are k-morphisms.
- `f`, `v`, `u'`, `f'` are the four maps; `sq : IsPullback ...` permits every
  Cartesian presentation, including the literal fibre product. The map `v`
  has no extra condition. `(d : ℕ) [SmoothOfRelativeDimension d f.left]`
  gives the smooth pure relative dimension, including zero. The compactification
  is `(c : Compactification f.left)`; the second one is literally
  `c.ofIsPullback sq`, with the same compactification at every coefficient level.
- The parameters `b : SpTowerShriek.Base l E`,
  `o : SpTowerShriek.Operations l E b`,
  `q : SpTowerCalculus.Coordinates l E b`, and
  `x : SpTowerShriek.OpenExchange l E b o` fix the dependency's geometric
  operations and their section-normalized presentations. Their data contain
  the specified ordinary adjunctions and comparison normalizations. They are
  not arbitrary arrows substituted for geometric functors. No preservation,
  normalized-tower, flatness, or exceptional-mate-invertibility hypothesis is
  attached to them.
- `SpTowerCalculus.C` is the already defined full category
  `spConstructibleTorTowerCategory`. It uses the ordinary derived category
  of the existing strict varying-ring towers, finite-level constructibility,
  and common cohomological and Tor intervals. It imposes no normalization.
  `Data` packages outputs specifying membership and the right adjoints with
  `SpTowerGluing.Levels`. The main theorem existentially supplies these data;
  their closure fields are conclusions, not added hypotheses.

### Every clause of the conclusion

- The exchange is the dependency's `SpTowerShriek.exchange`, transported by
  the existing realization equivalences. `composition` cancels only the
  middle equivalence with its specified counit. `exchange` applies that
  coordinate transport, and `beta` restricts this actual natural transformation
  to the full tower subcategories. The witness `hb : IsIso (beta ...)`
  is concluded by the theorem. No arbitrary exchange is a hypothesis.
- `Laws.exchange_evaluation` identifies the evaluation of this restricted
  exchange with `finiteExchange`, the exact
  `mixedCompactSupportExchange` on the same compactification. The square's
  chosen pullback identification is `sq.isoPullback`, with its projection
  equations. The equation includes the actual pullback evaluations and
  `Levels.support_evaluation` on both sides.
- `U` and `V` are restrictions of the existing
  `SpTowerCalculus.etalePullback`, whose definition takes an arbitrary
  morphism (it does not require that it be etale). Thus the source and target
  of `mate` are precisely `a.right ⋙ U` and `V ⋙ a.right'`, i.e. P and Q.
- `mate` is **defined** by Mathlib's `mateEquiv` of the two supplied
  adjunctions and the inverse of **this** beta. It is a natural transformation,
  so it includes naturality in the entire tower K. `Laws.transpose` states
  its component formula as the primed unit followed by the primed right
  adjoint applied to beta inverse followed by the pulled-back counit.
  Lean composition `≫` lists maps in application order.
- `finiteMate` is the finite primed adjunction's `homEquiv` applied to the
  inverse of `finiteExchange` followed by the pulled-back finite counit.
  `Adjunction.homEquiv_apply` is exactly the unit-followed-by-G formula in
  the node. `hfinite` concludes invertibility of the **compact-support**
  exchange at every finite ctf test object, which permits that inverse.
- `sourceComparison` and `targetComparison` are actual isomorphisms:
  `pullEvaluation` is built from `Geometry.pullEvaluation`, the realization
  counits and `SpTowerCalculus.levelComparison`; the two right-adjoint
  comparisons are `Levels.comparison`. Their adjunction normalizations are
  inherited from `Levels.unit` and `Levels.counit`. `Laws.evaluation` is the
  claimed equality of evaluated derived **morphisms** with the finite mate
  under precisely these isomorphisms. It is not a cohomology-only assertion.
- `coefficient` is `SpTowerGluing.coefficientMate` with the finite adjunctions
  and direct-image coefficient comparison of `Levels`, so it is exactly c^f,
  specified by its counit equation. `sourceCoefficient` applies u_m^* to it
  after `directImageScalarPullbackIso.inv`. `targetCoefficient` uses the
  primed coefficientMate, then G'_m of the same canonical scalar/pullback
  inverse on the input. These record, explicitly, the identifications
  suppressed in the node's displayed formulas.
- `inputReduction` is the actual `SpTowerCalculus.reduction` of K, bundled
  as a finite ctf morphism. `sourceReduction` and `targetReduction` are
  the actual reductions of P and Q conjugated by the two comparison
  isomorphisms. `Laws.source_reduction` gives u_m^*G_m(r) after u_m^*c^f;
  `Laws.target_reduction` gives G'_m(v_m^*r) after c^{f'}. In each formula
  the indicated pullback/scalar identification is inside the corresponding
  coefficient definition, so both equations have exactly the stated types.
- `Laws.mixed` states the cited mixed identity at the actual quotient,
  for every finite K_n. `Laws.reduction_chain` then states **three separate
  equalities**: T(e_n) followed by r^Q equals sourceCoefficient followed
  by e_m at TK_n followed by Q_m(r); that equals sourceCoefficient followed
  by P_m(r) followed by e_m at K_m; that equals r^P followed by e_m at K_m.
  These are exactly all four words in the node's displayed chain, including
  the middle word and the transition of K. The canonical comparisons are
  retained rather than replaced by arbitrary maps.
- Naturality in K uses actual functors, the natural transformation `mate`,
  natural finite exchanges, natural adjunction units/counits/comparisons and
  the existing natural tower reduction. All chain equalities quantify over
  the whole tower K. No input transition or exceptional mate is inverted.
  In particular, the theorem makes no `IsIso (mate ...)` claim.
- Every source and target is either an object of the existing full tower
  ctf categories (`Data`, `U`, `V`, both right adjoints), or the existing
  finite full ctf categories (`finiteP`, `finiteQ`, `inputReduction`, the
  scalar certificates in `Levels`). Thus the uniform-domain clause is retained.

### Dependency declarations used

| Node | Module and declarations read/used |
| --- | --- |
| def-weil-finite-field-fiber | `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension` supplies `coefficientExtensionIntegers` and the field-extension conventions |
| sk-def-sfb-dc-setting | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`: `CondensedRing.compactificationOverField`; the same Over/finite-type/separated conventions, with the arbitrary fixed compactification c retained |
| sk-def-sp-coefficient-towers | `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spEllIdeal`, actual ell-power quotient system |
| sk-def-sp-normalized-towers | `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spConstructibleTorTowerCategory`, `spFiniteConstructibleTorCategory`, `spDerivedCoefficientEvaluation`; normalized category read but not imposed |
| det-sp-coefficient-towers-abelian | `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `SpCoefficientTowersAbelian`, `sp_coefficient_towers_abelian`, specified reductions and their ordinary-complex normalization |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`, `SmoothOfRelativeDimension` |
| def-cbc-compact-support-square | `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`, `Compactification.baseChange` |
| det-sp-tower-shriek-levels | `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `Base`, `Operations`, `OpenExchange`, `exchange`, `Geometry.pullEvaluation` |
| det-sp-tower-gluing | `Sheaf.Paper.SmoothPurityTowerGluing`: `tower_gluing`, `support`, `level`, `Levels`, `coefficientMate`; its imported `CoefficientTowerShriekInterfaces` supplies `SpTowerCalculus.C`, `Coordinates`, `F`, `etalePullback`, `realization`, `levelComparison`, `quotient`, `reduction` |
| det-sp-reduction-exceptional | `Sheaf.SecSmoothPurity.ReductionExceptional`: `reductionExceptional_isIso`, `ReductionExceptionalRealization`, `reductionCtfScalar`, `reductionCtfCompactSupport`; the coefficientMate uses its specified counit-transpose comparison |
| det-sp-mixed-base-change | `Sheaf.SecSmoothPurity.MixedBaseChange`: `mixedBaseChange`, `mixedCompactSupportExchange`, `mixedCtfPullback`, `mixedPullbackCompactification`; imported `DirectImageScalarOperations` supplies `directImageScalarPullbackIso` |

The public imports explicitly include each recorded statement-dependency module.
The stated proof-only inputs are imported non-publicly:
`CompactSupportUniformTorBound` (det-sp-tower-bound-uniform), Mathlib's
`Morphisms.Etale` (lem-sbc-smooth-relative-dimension-permanence), and
`ScalarExtensionFunctor` (det-sp-scalar-extension-functor). I read their relevant
signatures as well. The proof-only
lem-sp-ctf-tower-pullback-reconstruction has no Lean record in the read checkout,
so there is no recorded module to import. It is cited, with its role, in the
complete six-step proof docstring; no object from that unstated proof-only lemma
is needed to type this statement and no substitute notion is introduced.

### Edge cases checked before writing and on rereading

- n=m, including n=m=0 in Lean (the paper's positive level one): all quotient,
  scalar-unitor and reduction normalizations are the existing dependency's;
  no strict inequality or positive-index omission occurs.
- Ramified E: the actual ell-power quotient R_n is used at every occurrence,
  not the unrelated uniformizer exponent n.
- Nonflat quotients, for example Z/ell^2 -> Z/ell: no Flat binder or
  underived tensor appears. The coefficient comparison is the derived one.
- Unnormalized towers and noninvertible transitions: every reduction is used
  only in its stated direction. Only beta, finite beta and the canonical
  comparison isomorphisms are inverted.
- Empty schemes, the zero object, d=0, identity base change and arbitrary
  nonflat base change: no nonempty-scheme, positive-dimension, flat-base-map
  or normalized-tower assumption is present.
- The sites retain object universe u+1, morphism universe u, and module
  coefficient universe u+1 from the existing dependency interfaces. No
  equality of site universes was imposed. Universes and variables are explicit;
  `set_option autoImplicit false` applies throughout.

### Searches for prior declarations

- `msearch.py ... leanfinder`, query: "Adjoint transpose of compact support
  tower base change evaluates to the finite transpose and commutes with quotient
  coefficient reductions". Eight hits: `IsBaseChange.toDualBaseChange`,
  `IsBaseChange.dual`, finitePow, toDualBaseChange_tmul, finsuppPow,
  of_fintype_basis, `LinearMap.polyCharpolyAux_baseChange`, toDual_comp_apply.
  These are linear-algebra base-change lemmas, not the tower mate statement.
- `msearch.py ... loogle`, query: `CategoryTheory.Adjunction.homEquiv`.
  Twelve hits, including homEquiv, homEquiv_apply/unit/counit,
  homEquiv_naturality variants through the foundational interface. These give
  generic adjunction tools but not the geometric tower evaluation/reduction result.
  The actual generic mate tool reused is Mathlib's `mateEquiv`.
- `msearch.py ... grep`, query: `tower.*mate|mate.*evaluation|coefficient.*reduction`,
  subdirectory `CategoryTheory`. Four hits, all in rigid monoidal duality:
  leftAdjointMate_comp_evaluation, rightAdjointMate_comp_evaluation and uses.
  No derived coefficient-tower result.
- `msearch.py ... leansearch`, query: "Exceptional base change counit mate for
  ordinary derived coefficient towers evaluates to finite coefficients and
  commutes with derived quotient reductions". Eight hits, including
  `CategoryTheory.Adjunction.derivedε`, its congr_simp theorem, a condensed
  profinite counit and linear-algebra base-change lemmas. No exact statement.
- `rg -n` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, queries:
  `towerMate|tower_mate|mate_evaluation|lem-sp-tower-mate-evaluation-reduction`
  and the prospective full namespace/name. No declaration of this item and
  no namespace/name collision. Read the nearby
  `Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars` (clopen proper/open
  constant-coefficient towers), `Sheaf.Paper.StrictTowerMateEvaluation`
  (strict augmented coefficient presentation), and
  `Sheaf.Paper.ConstantScalarTowerMates` (scalar restriction mates).
  They are different constructions, not the varying-coefficient ctf
  exceptional mate with the present complete reduction chain.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

### Validation

The complete module compiled through the prescribed `scompile.py` wrapper in
both sandbox mode and its actual library module name, cleanly with no warnings.
The sole expected postponed proof is the main theorem. Delivery preflight and
final compile results are recorded below after running the delivery tool.

## Second reading by Q15

(Second reading written by the maintainer's independent reviewer for Q15, replacing the
earlier same-session self-check; the Lean module and node records are unchanged.)

The node, read clause by clause against `tower_mate_evaluation_reduction` and its helpers:

1. Global datum k = F̄_q, ℓ ≠ p, E/Q_ℓ finite: `k : FiniteFieldDatum.{u}` (k.k is the
   algebraic closure of the finite field k₀, k.p its characteristic), `_hne : l ≠ k.p`,
   `(l) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional]`.
   Exact.
2. A_n = O_E/ℓ^n, n ≥ 1: `SpTowerShriek.R l E n = O_E ⧸ spEllIdeal^(n+1)` (Lean index n is
   the paper's n+1); ℓ-power, not uniformizer power, so ramified E is kept. Exact.
3. Separated finite-type k-schemes, k-morphisms: four `Over (Spec k.k)` objects with
   IsSeparated/LocallyOfFiniteType/QuasiCompact structure maps; f, v, u', f' are Over maps.
   f is then separated and of finite type automatically. Exact.
4. C_T = uniformly bounded constructible finite-Tor strict towers, unnormalized:
   `SpTowerCalculus.C = spConstructibleTorTowerCategory` (recorded in
   def-sp-coefficient-tower-shriek-interfaces, used by det-sp-tower-gluing). No
   normalization field anywhere. Exact.
5. r^D_{n,m}: `SpTowerCalculus.reduction` with `q.scalar` (adjunction-normalized scalar
   coordinates), bundled as `inputReduction`; h : m ≤ n includes m = n. Exact.
6. f smooth of pure relative dimension d ≥ 0: `(d : ℕ) [SmoothOfRelativeDimension d f.left]`.
   v arbitrary, `sq : IsPullback u'.left f'.left f.left v.left` (any Cartesian
   presentation). Exact.
7. Compactification f = pj and its pullback: `c : Compactification f.left` and
   `c.ofIsPullback sq` at every level (also inside `finiteExchange` via
   `mixedPullbackCompactification`, which the exchange_evaluation typing identifies with it).
8. F_f, G_f, units/counits from shriek-levels and gluing: `SpTowerGluing.support` of the
   transported `SpTowerShriek.F`, and `Data.right/adjunction/levels` (and primed). As in the
   recorded `tower_gluing`, the right adjoint and its `Levels` are existential outputs;
   `Levels.comparison` is pinned by the counit and unit equations and
   `support_evaluation` by `Evaluation.normalization` (Fcomparison), so the right adjoint is
   only determined up to the unique adjunction-compatible isomorphism, under which every
   clause of `Laws` is invariant. Not a weakening.
9. β the actual compactification exchange, restricted to C, evaluating to β_n:
   `exchange` = `SpTowerShriek.exchange x sq c` conjugated by the realization equivalences
   (`composition` cancels only the middle equivalence with invFunIdAssoc), `beta` its
   full-subcategory restriction, `hb : IsIso beta` concluded. `Laws.exchange_evaluation`:
   I checked every arrow: ev_n(β_M) ≫ comparison' = pullEvaluation_v ≫ v_n^*(comparison) ≫
   β_n(ev_n M) ≫ F'_n(pullEvaluation_u'⁻¹). β_n = `mixedCompactSupportExchange` (proper
   exchange then open base change), the finite map of det-sp-mixed-base-change. The finite
   invertibility `hfinite` is concluded only at G_{f,n}K_n, where finite base change holds.
   b, o, x, q are universally quantified as in the landed `tower_gluing`; their fields are
   HEq-pinned to the generic calculus, and IsIso β follows from `Base.calculus.detects`
   plus finite base change, so no `SpTowerShriek.Laws` hypothesis is needed.
10. P_K, Q_K, q_K, e_K = G'(q_K)∘η': `U`, `V` restrict the actual pullbacks;
    `mate = (mateEquiv adj adj' (inv β)).natTrans : right ⋙ U ⟶ V ⋙ right'`; Mathlib's
    mateEquiv convention gives the component unit'_{U(GK)} ≫ G'(β⁻¹_{GK} ≫ V(ε_K)),
    which is `Laws.transpose` and the node's formula. Naturality in K is built in.
    No IsIso of the mate is asserted. Exact.
11. Evaluated map e_n: `finiteMate` = finite primed homEquiv of (β_n⁻¹ ≫ v_n^*ε_n), i.e.
    G'_n(v_n^*ε_n ∘ β_n⁻¹) ∘ η'_n; `Laws.evaluation` equates ev_n(e_K) with it under
    `sourceComparison` (pullEvaluation then u_n^* of Levels.comparison) and
    `targetComparison` (Levels'.comparison then G'_n of pullEvaluation). An equality of
    derived morphisms, not of cohomology. Exact.
12. r^P = u_m^*G_m(r) ∘ u_m^*c^f, r^Q = G'_m(v_m^*r) ∘ c^{f'}(v_n^*K_n): `source_reduction`
    and `target_reduction`, with r^P, r^Q the actual reductions of P_K, Q_K conjugated by
    the comparisons; c^f = `coefficientMate` (counit transpose specified in gluing /
    det-sp-reduction-exceptional); the suppressed T∘pullback identifications are
    `directImageScalarPullbackIso.inv` (canonical, def-sp-constant-scalar-pullback-
    comparison), oriented scalar-then-pullback → pullback-then-scalar. Exact.
13. Mixed identity c^{f'} ∘ T(e_n) = e_{m,TK_n} ∘ u_m^*c^f: `Laws.mixed`, every finite K_n
    (no flatness of A_n → A_m). Exact.
14. The chain of four words: `reduction_chain` is three conjunct equalities
    T(e_n) ≫ r^Q = c ≫ e_m(TK_n) ≫ Q_m(r) = c ≫ P_m(r) ≫ e_m(K_m) = r^P ≫ e_m(K_m), all
    four words of the node in application order, for every tower K and m ≤ n. Exact.

Edge cases: m = n (h = le_refl), Lean n = 0 (paper level 1), ramified E (ℓ-power ideal),
nonflat quotients (derived scalar extension only), unnormalized K and non-invertible
transitions (only β, β_n and comparison isomorphisms inverted), d = 0, empty schemes,
v arbitrary (identity, non-flat), K = 0. Universes: one u for schemes and E, sites and
coefficients as in the dependency interfaces; no extra universe equation.

Records: lean.statement equals the file signature verbatim; lean.declarations equals the
22 declarations of the file; the item differs from live only in `lean`; stmt_deps
unchanged. All helpers are real data (no sorry); one theorem, proof `sorry`; every
declaration has source and blueprint docstrings; the statement docstring carries the six
proof steps. Searches: besides the worker's, grep for `SpTowerMate`/`tower_mate`/the
item id in the live side `lean/Sheaf` and `lean/WeilConjectures` trees: hits are the
constant-coefficient `StrictTower` modules (TowerMateEvaluationScalars,
TowerOpenBetaNormalization, StrictConstantTowerOperations ...) and a private lemma in
StrictQuotientExchangeUnitEquation; none states the varying-coefficient ctf mate with
this reduction chain, and no `SpTowerMate` namespace exists.
Uncited definition owners (def-sp-coefficient-tower-shriek-interfaces for SpTowerCalculus.*,
def-sp-constant-scalar-pullback-comparison, def-sp-reduction-direct-image-comparison,
def-weil-pbc-proetale-operations) are definition nodes reached through cited dependencies:
advisory only. Advisory for stage 3: the recorded `tower_gluing` gives the adjunction only
for `compactificationOverField f`; the item, like its node, uses an arbitrary c and its
pullback, so the proof needs compactification independence of F.

Mismatches found: none in the statement or records. Change: this section only.
