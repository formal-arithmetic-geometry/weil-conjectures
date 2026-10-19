## Worker report

The module `Sheaf.Paper.ContinuousRationalDerivedRealization` states
`AlgebraicGeometry.Scheme.ContinuousRational.continuous_rational_derived_realization`.
Its conclusion is the existence of one compatible `Family`, not separate unrelated
existence claims. The only postponed proof is this theorem. Its docstring contains
all seventeen proof steps of the DAG node, including their dependency identifiers.
The auxiliary definitions and structures unpack this node's own constructions and
comparison normalizations. Their data contain no `sorry`.

The node's statement is unchanged. Three already recorded nodes are added to
`stmt_deps`: `def-weil-pbc-continuous-constructible-module`,
`lem-weil-pbc-continuous-coefficients-immersion-restriction`, and
`prop-weil-pbc-scalar-extension`. Their existing notions and canonical maps are used
instead of private replacements. No new node or dependency module is delivered.

### Hypotheses and clauses

All names below are in `AlgebraicGeometry.Scheme.ContinuousRational` unless qualified.

| Node text | Lean rendering |
| --- | --- |
| Prime ℓ | The theorem's `(l : ℕ) [Fact l.Prime]`. |
| Finite E/ℚℓ | `Family.realization` quantifies over every `A : Type u` with `[Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]`. There is no extra chosen norm or topology hypothesis. |
| Valuation ring and uniformizer | The recorded `PbcIntegralRing l E`, `pbcIntegralDatum l E`, and `pbcUniformizer l E`; continuous coefficients use the canonical coefficient-extension absolute value. |
| Noetherian scheme | `Base.scheme : Scheme.{u}` and `[Base.noetherian : IsNoetherian scheme]`. |
| Finite dimension | `Base.dimension : ∃ n : ℕ, topologicalKrullDim scheme ≤ n`; no fixed global dimension bound. |
| ℓ invertible on the scheme | `Base.prime_unit : ∀ x, IsUnit (l : scheme.presheaf.stalk x)`. It is not a characteristic restriction on an unrelated ground field. |
| Small pro-étale site | `Scheme.ProEt` and `ProEt.topology`, with objects in universe `u+1` and morphisms in `u`; module and coefficient sheaf carriers use `u+1`. |
| B is the limit of finite quotient constant sheaves | `pbcAdicCompletion` and `pbcAdicProjection` are the existing actual limit and projections. `At.integralIso`, `finiteIso`, `finite_normalization`, and `integral_normalization` identify them with continuous functions and fix all finite quotient reductions, including constants. |
| E is sheaf localization of B | `At.localizationIso` identifies the existing `integralCoefficientLocalization` (sheafified sectionwise localization) with `rationalCoefficientSheaf`. `localization_normalization` fixes numerators; `inclusion_normalization` fixes integral continuous functions. This is sheaf localization, not objectwise localization asserted to be a sheaf. Its underlying module localization is the sequential sheaf colimit of repeated uniformizer multiplication. |
| Continuous coefficients and their topology | The existing `integralCoefficientSheaf` and `rationalCoefficientSheaf` have actual continuous-function sections. `At.encoding` and its value normalization compare the equivalent `WithAbs` encoding required by the recorded constructibility predicate. |
| Finite locally closed stratification | `At.strata_criterion` uses the recorded `FiniteLocallyClosedStratification` and its actual immersion maps. |
| Pro-étale locally finite free restrictions, variable finite rank | `At.strata_criterion` uses `SheafOfModules.IsFiniteLocallyFree` on each actual inverse image. `IsConstructible` reuses `AlgebraicGeometry.ProEtale.IsContinuousConstructible` via normalized coefficient restriction. Over a field its finitely presented local models are precisely finite free models. There is no fixed rank across strata or connected components. |
| Ambient bounded constructible derived category | `IsDerivedConstructible` is the `ObjectProperty` of ambient `DerivedCategory (pbcModules X E_X)` requiring some integer lower and upper bound and constructibility of every actual `DerivedCategory.homologyFunctor` object. |
| Raw rationalization, completed integral category, étale witnesses | `At.J` starts at the existing `PbcRationalCategory`; `At.integral` uses the existing `PbcIsBoundedConstructibleComplete` full subcategory, so its completeness and compatible étale origins are retained. No Karoubi completion is used. |
| J(QK) = E ⊗ᴸ_B K | The natural isomorphism `At.integral` compares `pbcRationalization ⋙ J` with the actual derived change-of-rings `pbcDerivedExtend (integralIso.hom ≫ inclusion)`. |
| J(f/varpi^n) = varpi^(-n) J(f) | `At.fractions` states the stronger equivalent pure-localized-scalar formula for every integral arrow and every element of `Localization.Away (pbcUniformizer l E)`, using the recorded `pbcRationalCoefficientEquiv`. |
| E-linear equivalence of triangulated categories onto the full subcategory | `At.linear : J.Linear E`, `At.additive`, `At.shift`, `At.triangulated`, bijectivity on every Hom in `At.fully_faithful`, and the exact essential-image biconditional `At.image`. These assert an equivalence with exactly the full subcategory defined above. |
| Both localized t-structure bounds, all degrees | `localizedT` reuses `pbc_localized_tstructure`; `At.t_bounds` asserts both biconditionals at every integer degree. The choice is of the uniquely specified t-structure classes, not of arbitrary object data. |
| Heart consists exactly of constructible modules in degree zero | `At.heart` is the biconditional with a constructible sheaf and an isomorphism to `DerivedCategory.singleFunctor _ 0`. Essential surjectivity onto every such sheaf follows from `At.image` and this biconditional. |
| Degree-r cohomology formula | `localizedCohomology` uses actual localized truncations and shift by r. `At.cohomology` is a natural isomorphism to ordinary `DerivedCategory.homologyFunctor _ r`, ordinary coefficient extension `pbcExtend`, and placement in degree zero. |
| Arbitrary g between schemes with the same geometric hypotheses | `Family.along` quantifies over every morphism between `Base l` objects. No smoothness, flatness, étaleness or immersion hypothesis is imposed here. |
| Actual coefficient structure map, not an assumed isomorphism | `Along.coefficient`, its continuous-function adjunct in `normalized`, and its square with `completedCoefficientMap` specify the actual map `g⁻¹E_Y → E_X`. |
| Ordinary derived module inverse image | `derivedPull g c` is literally `adicTowerPullback g R ⋙ pbcDerivedExtend c`. The first is exact inverse image of coefficients; the second is derived tensor along the actual structure map. `Along.counit`, `normalized_counit`, `universal`, and `computes` identify its ordinary module functor on K-flat complexes. `IsNormalizedPullCounit` fixes the exact identity-tensor transport and the counit itself by multiplication and the existing `pbcComplexCounit` on all complexes. |
| Completed raw pullback under J | `integralPull` aliases the existing `pbcConditionalIntegral` restriction of `pbcActualCompletedPull`, with preservation asserted in `Along.integral_mem`. `rawPull` aliases the existing `pbcConditionalRational`, whose Hom map is `ScalarLocalization.transport`. `Along.comparison` is a natural isomorphism with `J ⋙ derivedPull`. |
| Canonical comparison before and after completion | `Along.balance_sections` fixes ordinary balancing on tensor units. `balanceComplex_components` and `ambient_normalization` fix the derived comparison on flat K-flat representatives. `completion_unit` fixes the rational comparison using the actual ordinary-to-completed unit and `At.integral`. |
| Identity and composition of scheme morphisms | `Family.identity` and `Family.composition` provide `Identity` and `Composition`. Their coefficient equation, tensor-unit sections, derived-counit normalization and comparison diagrams use the actual fibre-product identity and composition maps and ambient derived module inverse images. |
| Finite coefficient extension | `Family.fieldChange` quantifies over every finite coefficient-field algebra embedding. `FieldChange.normalized` fixes its pointwise map on continuous sections; `square` fixes compatibility with the recorded integral scalar coefficient map; `comparison` is normalized on integral representatives by `pbcReductionNormalization`. |
| Coefficient associators and coherence | `FieldComposition.compatibility` uses the existing `pbcRationalScalarCompComponent` and ambient balanced `pbcReductionNormalization`, for all embeddings including identities and repeated fields. Thus iterated comparisons use the existing unital associative tensor comparisons and their pentagon, not unrelated associators. |
| Mixed scheme/field extension compatibility | `Mixed` fixes the coefficient square and ordinary balancing formula, derived balancing on K-flat representatives, the actual `pbcScalarCompletedPullIso` on raw integral representatives, and the square with both J comparisons. |
| Étale or locally closed immersion | `Along.special` takes `Etale g ∨ IsImmersion g` and concludes the coefficient map is an isomorphism and ordinary module inverse image preserves finite limits and colimits. Together with the left-derived universal counit this identifies derived inverse image with the exact ordinary functor. |
| Any pro-étale site object, without finiteness on its source | `Family.siteRestriction` quantifies over every `U : X.scheme.ProEt`, with no noetherian, dimension, or prime-unit binder on `U.left`. `SiteRestriction.slice` is fixed by `siteInclude`; `ring_normalization` fixes continuous functions. Its comparison is literally `SheafOfModules.overFunctor ⋙ SheafOfModules.pushforward` along that slice equivalence and ring map. `comparison_units` fixes it on the actual projection `siteCounit`. Finite-limit/colimit preservation gives exactness. |
| Restriction also for the ambient displayed pullback | `SiteRestriction.derived` identifies the same `derivedPull U.hom coefficient` with the exact ordinary functor's `mapDerivedCategory`. `derived_normalization` fixes its components against `mapDerivedCategoryFactors` and its universal counit; `normalized_counit` fixes that counit by the actual balanced identity-tensor map. |
| All comparisons come from finite maps, localization, balanced tensors | Finite and integral normalizations in `At`; normalized localization and inclusion; coefficient squares in `Along`, `FieldChange`, `Mixed`; section formulas and K-flat counit equations in `Along`, `Composition`, `Identity`, `Mixed`, and `SiteRestriction`. |

The fields containing additivity, linearity, shift and exactness witnesses are
conclusions of the existence theorem, not extra hypotheses on the schemes or fields.
Similarly `At.topNoetherian` supplies the true underlying-space property needed by
the already recorded constructibility API; it is not a hypothesis of the main theorem.

### Dependency declarations used

The full signatures and docstrings of the original statement dependencies were read.
The imported modules below supply the declarations, sometimes through public imports:

| Dependency | Module and declaration |
| --- | --- |
| Finite coefficient extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, with the coefficient integers, absolute value and finite-quotient APIs. |
| Small site | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`. |
| Completed coefficient datum | `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, `pbcAdicCompletion`, `pbcAdicProjection`. |
| Module sheaves | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; `Sheaf.Paper.PbcRationalCategory`: `Scheme.pbcModules`. |
| Ambient derived category | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`. |
| Stratification | `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`: `Scheme.FiniteLocallyClosedStratification`. |
| Cohomology | `Sheaf.Paper.PbcQbarStandardCohomology`: `Scheme.pbcQbarCohomology` and its public ambient homology/truncation API; the actual ambient coefficient category uses `DerivedCategory.homologyFunctor`. |
| Raw category | `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`, `PbcRationalCategory`, `pbcRationalization`. |
| Integral category | `Sheaf.Paper.IntegralUniformCoefficient`: `pbcBoundedConstructibleComplete`, `PbcIsBoundedConstructibleComplete`. |
| Localized t-structure | `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`. |
| Completed pullback | `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarCompletedPull` and its public actual integral API `pbcActualCompletedPull`, `pbcActualCompletedPullUnit`, `pbcActualDerivedPull`, `pbcActualModulePull`. |
| Derived change of rings | `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the public canonical APIs are `pbcDerivedExtend`, `pbcComplexCounit`, `pbcReductionNormalization`. |
| General inverse image | `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`, `adicTowerInverseImage`, `proEtaleModuleInverseImage`, `adicTowerPullback`, `proEtaleSheafAdjunction`. |
| Existing continuous constructibility | `Sheaf.Paper.ContinuousConstructibleModule`: `AlgebraicGeometry.ProEtale.IsContinuousConstructible`, `latticeCoefficientSheaf`. |
| Continuous coefficients | `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`: `integralCoefficientSheaf`, `rationalCoefficientSheaf`, `integralCoefficientLocalization`, their value and normalization predicates. |
| Scalar extension | `Sheaf.Paper.PbcScalarExtension`: `pbcEmbeddingIntegralTensor`, `pbcRationalScalarExtension`, `pbcRationalScalarCompComponent`, `pbcScalarCoefficientMap`, `pbcScalarCompletedPullIso`, and the existing raw E-linear structure. |

The recorded proof-dependency modules that are available are imported as well,
including the finite filtration/lattice, scalar Hom, localization coherence,
open-closed, t-structure, and ringed comparison ingredients. The module's theorem
docstring names every dependency used by each original proof step.

### Edge cases

Checked the statement on the empty scheme and zero sheaves/complexes: `Base.dimension`
is existential, a stratification may have zero members, no rank is required to be
positive, and all integer cohomology degrees are allowed. No nonempty-space or
positive-rank condition is added. The zero raw object and uniformizer-torsion
objects can map to zero; full faithfulness is asserted only after raw localization.
Finite quotient index `n = 0` denotes the first quotient (power `n+1`), matching the
recorded tower. The dimension bound may be zero. Identity scheme maps, identity
field embeddings and repeated coefficient fields occur in the quantified families.
The arbitrary pullback clause has no assumption that its coefficient map is an
isomorphism; that conclusion is isolated to étale/immersion and site-object cases.
A site object may have a non-noetherian source and is not packaged as `Base`.
No equality between the small site's object and morphism universes is imposed.

### Searches

The prescribed `msearch.py` calls were made and logged in `searches.jsonl`:

- LeanFinder: `The rational localization of bounded constructible adic sheaves is equivalent to bounded constructible derived continuous coefficient module sheaves`. Eight generic condensed/cohomology results, no realization statement.
- Loogle: `CategoryTheory.Equivalence, DerivedCategory, SheafOfModules`. No hits.
- Mathlib grep: `continuous.*realization|rational.*realization|Dcons`. Returned generic unrelated results; no exact statement.
- LeanSearch: `Rational constructible adic complexes are equivalent to bounded constructible derived continuous coefficient module sheaves`. Eight hits concerning adic completions, condensed discreteness, continuous cohomology and abelianness; no exact realization.
- `rg` of the upstream `WeilConjectures` tree for continuous/rational realization names and the item id: no exact result.
- `rg` of `lean/Sheaf` found `CondensedERealization` and `AdicHeartPullbackFibres`. Their geometric interfaces are restricted to separated finite-type schemes over a ground field; they do not state this node for arbitrary noetherian finite-dimensional schemes and arbitrary morphisms. The generic continuous constructibility and coefficient definitions found in this search are reused directly.

The Bhatt--Scholze source was read at 6.8.2, 6.8.11, 6.8.14 and 6.8.15; the module
follows the current node's expanded canonical-comparison statement. No statement
correction or unresolved mathematical dispute was found.

## Second reading by Q20

I re-read the node and the final interface clause by clause, including all comparison
normalizations. This is a self-check, not a claim of an independent second agent:
the dispatch brief explicitly prohibits starting other agents and says the
maintainer independently reviews this delivery. In this reading I made E-linearity
explicit, normalized the slice restriction comparison on tensor units, and added
its exact derived-functor comparison. A final check fixed both inverse-image counits
by `IsNormalizedPullCounit` and replaced the raw/integral adapters with aliases of
the published conditional-restriction definitions. I checked that no hypothesis on the source of
a general site object slipped into the statement. The complete original proof plan
was copied into the theorem docstring. The only `sorry` is the node's theorem.

Validation uses only the required `scompile.py` and `deliver2.py` wrappers; no direct
git command, live-library edit, or global build was run.
