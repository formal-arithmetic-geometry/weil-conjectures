## Worker report

The module `Sheaf.Paper.RationalStratumPullbackModels` states
`AlgebraicGeometry.Scheme.RationalStratumPullback.rational_stratum_pullback_models`.
The node is unchanged outside `lean`. No new nodes or dependency repairs are needed.
The only postponed proof is the main theorem, whose docstring contains all six DAG
proof steps and their uses. Definitions contain real constructions; structures describe
the comparison data whose existence is the assertion of this node.

The source read was Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.8.2
(p. 58), Definitions 6.8.3/6.8.6/6.8.8 (pp. 59--60), and Remark 6.8.15 (p. 62).
The current blueprint's `lem-per-smooth-pullback-t-exact.proof.md`, first paragraph,
was read as well: this node supplies the locally free chart calculation for its
cohomological pullback assertion. The source explicitly defines continuous coefficients
for any scheme before the noetherian restriction used for constructibility.

Hypotheses and objects, in order:

| Node text | Lean rendering |
| --- | --- |
| A prime ell | `l : ℕ`, `[Fact l.Prime]`, bound explicitly in the public section |
| Algebraic closure Omega, finite intermediate coefficient field E | `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, `_embedding : E →ₐ[ℚ_[l]] Ω`. A field algebra hom is injective, so this is an intermediate field with its inclusion, independently of the algebraic closure's universe. No condition on the embedding beyond being a coefficient-field inclusion is added. |
| Valuation ring and chosen uniformizer | The published `pbcIntegralDatum l E`, `pbcUniformizer l E`, and `Padic.coefficientExtensionIntegers l E`, with the spectral topology already fixed by the dependencies. |
| Noetherian finite-dimensional X,Y, ell invertible | `X Y : ContinuousRational.Base l` bundles exactly `IsNoetherian`, a finite `topologicalKrullDim` bound, and invertibility in every stalk. Empty schemes satisfy these same conditions. |
| Any scheme morphism | `g : Y.scheme ⟶ X.scheme`; there is no flatness hypothesis. |
| Small pro-etale site and completed integral category | The dependencies' `Scheme.ProEt`, `PbcBoundedConstructibleComplete`, `PbcIsBoundedConstructibleComplete`, and the actual completed coefficients used in `ContinuousRational.At` and `Along`. Their predicate includes intrinsic completeness, uniform constructible reductions, and compatible etale-origin witnesses. |
| Continuous rational realization J_X,J_Y | `aX : ContinuousRational.At l E X`, `aY : ContinuousRational.At l E Y`. These include the normalized equivalence with the full ambient bounded constructible subcategory and the localization formula. |
| Specified completed pullback, its gamma, and fraction extension | `a : ContinuousRational.Along l E g aY aX`, `(a.raw l E)`. These use `pbcActualCompletedPull`, not an alternative functor. The existing `a.completion_unit` law ties `a.comparison` to the actual completion unit and normalized integral structural maps. |
| Constructible E_X-module F | `F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)` and `_hF : ContinuousRational.IsConstructible l E X.scheme aX.encoding F`. The dependency's `aX.strata_criterion` identifies this predicate with local finite freeness on a finite locally closed stratification. |
| Raw rational object K, with J_X K isomorphic to F[0] | `K : PbcRationalCategory ...` and `_eK : aX.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F`. No Karoubi envelope occurs. |
| Any locally closed immersion on which F is locally finite free | `S : Scheme`, `i : S ⟶ X.scheme`, `[IsImmersion i]`, `_hS : ((ContinuousRational.modulePull i (coefficient l E i)).obj F).IsFiniteLocallyFree`. No smoothness, reducedness, or choice of supporting stratification is imposed. |
| S' and its projections | The actual `pullback g i`, `pullback.fst g i : S' ⟶ Y`, and `pullback.snd g i : S' ⟶ S`. This is Y times_X S with its scheme structure. |

Each conclusion and its normalization:

* The theorem supplies `m : Stratum l E g aX aY a i`.
  `m.square` is a natural isomorphism of ambient derived functors: invert the
  left composition, use `pullback.condition`, then apply the right composition.
  `m.comparison l E F K _eK` is the displayed isomorphism in the node. Its source
  is derived restriction of `aY.J.obj ((a.raw l E).obj K)` to S'; its target is
  `derivedPull g_S` of the single complex of the actual module restriction of F.
  Its definition first restricts `a.comparison.app K`, then uses `m.square`, then
  maps the supplied `_eK` and the exact-inclusion counit. Thus its naturality
  is inherited from actual natural transformations, relative to the specified
  identification of K, rather than an unrelated pointwise isomorphism.
* `coefficient` is the constructed `continuousCoefficientPullback` map, not a
  variable structural map. `scalarImage` is its adjoint on sections: actual
  precomposition with the first fibre-product projection. This gives precisely
  the continuous-function coefficient rings on all chart schemes.
* `Composition.coefficients` fixes the coefficient composite; `units` fixes the
  ordinary map on actual inverse-image/tensor units; `components` makes its
  complex map termwise that ordinary map; `normalization` fixes its ambient
  derived map on flat-term K-flat representatives. `Pull.normalized` and
  `Pull.universal` retain the normalized derived counit. These are the ambient
  composition comparisons of the node, with no realization on a chart scheme.
* The theorem quantifies over **every** `U : S.ProEt`, **every** `r : ℕ`, and
  **every** specified trivialization `e` of the actual restriction to U as the
  existing `SheafOfModules.free (ULift (Fin r))`. It supplies a `Chart` for these
  exact data. U' is `(proEtaleBaseChange g_S).obj U`, and g_U is
  `pullback.fst U.hom g_S`. Neither U nor U' has a noetherian hypothesis.
* `FreeModel.forward` states the balanced map on a general finite coordinate
  expansion: `a • moduleUnit (∑ j, b j • basis j)` goes to
  `∑ j, (a * scalarImage (b j)) • basis j`.
  Here `moduleUnit` is the actual inverse-image unit followed by `1 tensor -`.
  Thus this is `a tensor (b_j) ↦ (a g_U♯(b_j))`. Inverse-image sections are
  locally generated by those units; balancing and sheafification extend this
  equation to the sheaf tensor product. It is not an unconstrained map.
  `FreeModel.backward` gives the inverse on every `a e_j` as
  `a • moduleUnit (basis j)`, namely `a tensor e_j`.
* `FreeModel.derived` is defined by the canonical derived-to-ordinary counit
  followed by the ordinary balanced isomorphism in degree zero.
  `Chart.right` first uses the normalized chart square, then the given e,
  then this same `FreeModel.derived`. `Chart.left` is defined by restricting
  `m.comparison` and composing with `Chart.right`. Both sides therefore identify
  with the **same** `free E_U' r [0]`, and the displayed stratum isomorphism
  restricts compatibly with those two identifications.
* The two conjuncts `.IsGE 0` and `.IsLE 0` give concentration in degree zero of
  the left side on S'. They concern the actual realized completed pullback.

Dependency declarations read and used (all with their full signatures/docstrings):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, together with the imported valuation
  ring, uniformizer and quotient constructions of `CoefficientExtension`.
* `def-weil-scheme-morphism-properties` is explicitly a convention record with
  no declaration. Scheme morphisms and `AlgebraicGeometry.IsImmersion` are used
  directly; the latter is the locally closed immersion definition in Mathlib.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, actual completed
  ring and finite quotient maps; retained through the realization's integral model.
* `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`,
  specializing the three-clause `PbcBoundedConstructibleComplete` predicate.
* `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded `pbcQbarCompletedPull`
  imports the finite-stage `pbcActualCompletedPull` and its completion unit.
  The finite-field operation used here is exactly `Along.raw`, whose integral
  underlying functor is that `pbcActualCompletedPull`.
* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `PbcRationalDerivedCategory`, `pbcRationalization` (raw scalar localization).
* `Sheaf.Paper.ContinuousConstructibleModule`:
  `AlgebraicGeometry.ProEtale.IsContinuousConstructible`; reused through
  `ContinuousRational.IsConstructible` and its normalized coefficient encoding.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`; used by the realization's exact
  `strata_criterion`, without adding constructibility to the stratum definition.
* `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `continuous_rational_derived_realization`, `Base`, `At`, `Along`, `Along.raw`,
  `modulePull`, `derivedPull`, `moduleUnit`, `IsNormalizedPullCounit`. The specified
  normalized At/Along data are parameters, not replacement realization choices.
* `Sheaf.Paper.ContinuousCoefficientSliceNormalization`:
  `continuous_coefficient_slice_normalization`, `ExactPull`, `ModuleComparison`,
  `Ambient`; their arbitrary-chart restriction and counit normalization are the
  exact restriction API used in the proof plan.

The modules of all recorded proof dependencies are imported plainly, including
`RingedDerivedMonoidalComparisons`, `RingedTopoiDerivedPullbackIndependent`,
`FlatOnSite` (publicly inherited), `KFlatIndependentCoefficients`,
`CochainTensorUniverses`, `RingedSiteModules`, and the Mathlib immersion, weakly
etale, and fpqc covering modules. No new canonical tensor or inverse image is defined.
The helper names only assemble the existing operations and express this node's
normalization data.

Edge cases checked before writing: r=0 (the source and target are the free sheaf
on the empty type and the displayed sums are empty), F=0, K realizing zero,
empty S and empty S', and nonreduced fibre products. The chart quantifiers are
unrestricted by noetherianness, dimension, or coefficient flatness. Ranks may
vary between charts. No invertibility, prime, or empty-scheme case is suppressed
by a nonempty scheme or positive-rank binder. The scheme object and morphism
universes remain those of the small pro-etale framework, and coefficients use
its u+1 module universe. Omega has an independent universe v.

Searches actually run:

* `msearch.py ... leanfinder`: "Derived pullback of a finite locally free
  continuous coefficient sheaf on a pro etale stratum is finite free in degree
  zero on arbitrary trivializing charts". Eight results concerned etale
  morphisms/rings; none identified realized rational completed pullback.
* `msearch.py ... loogle`: `SheafOfModules.pullbackObjFreeIso`. Five hits gave
  the ordinary free-module pullback isomorphism and basis/naturality lemmas.
  Read Mathlib `Sheaf/PullbackFree.lean:113-142`: these do not give the derived
  realization or stratum assertion. The module imports that existing API.
* `msearch.py ... grep`: `pullbackObjFreeIso|freeFunctorCompPullbackIso`.
  Five hits in the same Mathlib module, the same ordinary comparison only.
* `msearch.py ... leansearch`: "Derived inverse image of finite locally free
  continuous sheaves on pro etale charts is concentrated in degree zero".
  Eight hits included sheaf pushforward composition evaluations and ordinary
  free pullback basis maps, not this statement.
* `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `rational.stratum|stratum.pullback|lem-per-rational-stratum-pullback-models`
  found the different integral-filtration model module and no exact declaration.
  A further `rg` for `rational_stratum_pullback_models` and its namespace in both
  trees and `dag/lean_names_upstream.json` found no pre-existing name.

Validation: `scompile.py Q46 lem-per-rational-stratum-pullback-models` passed both
sandbox compilation (33.6 seconds) and final-module compilation (29.4 seconds),
with no errors or unexpected warnings. `autoImplicit` is false; universes u,v and
all variables are explicitly bound. All source files and the shared DAG were
read only. No library or global build was run.

## Second reading by Q46

Author's separate statement audit; the maintainer performs the independent review.
Read the node and the final Lean together after compilation. Matched the prime,
finite coefficient field/inclusion, base hypotheses, raw object and its given
realization, arbitrary immersion, and local freeness against the binders above.
Traced `Stratum.comparison` through the specified Along comparison, both ambient
compositions and the exact-inclusion counit. Traced `Chart.right` and `Chart.left`
through the same fibre-product square and the given chart trivialization. Checked
that the balanced forward formula, basis inverse, rank-zero sums, and the two
cohomological bounds are present. The first compile exposed only elaboration
issues: additive structure must be carried explicitly with a normalized Pull,
and the continuous scalar image needs an explicitly typed section wrapper.
Those were repaired without changing the mathematical statement. There are no
statement corrections, new DAG nodes, dependency replacements, or disputed claims.
