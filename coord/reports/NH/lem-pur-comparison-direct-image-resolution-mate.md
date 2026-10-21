## Worker report

The module `Sheaf.AlgebraicGeometry.ComparisonDirectImageResolutionMate` states
`AlgebraicGeometry.ProEtale.comparison_direct_image_resolution_mate`, with `sorry`.
The seven preceding helpers contain real constructions; none chooses an arbitrary map,
adjunction, resolution or comparison isomorphism. The node is unchanged except for `lean`.
No new nodes or dependency repairs are needed.

Hypothesis and clause correspondence:

- Finite discrete commutative coefficients: `Λ : Type (u + 1)`, `[CommRing Λ]`,
  `[Finite Λ]`. Discreteness is the ordinary fixed-ring module coefficient encoding.
- Common larger universe and sites: `U V : Scheme.{u}` and
  `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, respectively
  `Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)`. This is the six-functor
  encoding fixed in STATE, with the site object and morphism universes retained.
  `CochainComplex.Plus` and `DerivedCategory.Plus` are the standard full subcategories.
- The morphism is `f : U ⟶ V`, `[QuasiCompact f]`, `[QuasiSeparated f]`.
- The sheaf is `F`; `comparisonResolutionSingle F` is exactly `F[0]`, built with
  `CochainComplex.singleFunctor`, together with its derived boundedness proof.
- `I`, `J` are arbitrary bounded below complexes in the two specified module categories.
  `[I.obj.IsStrictlyGE 0]`, `[J.obj.IsStrictlyGE 0]` say nonnegative;
  `[∀ n : ℤ, Injective (I.obj.X n)]` and its J counterpart say termwise injective;
  `[I.obj.IsKInjective]` and `[J.obj.IsKInjective]` say K-injective.
- `i : (comparisonResolutionSingle Λ F).obj ⟶ I.obj`, `[QuasiIso i]` and
  `t : A_U(I) ⟶ J.obj`, `[QuasiIso t]` are the two augmentations as stated.
- `A_T`, `N_T` are the published `comparisonUpperStar`, `comparisonLowerStar`;
  `comparisonAdjunction` supplies their specified unit and Hom bijections.
  `comparisonResolutionAdjunct` is h, computed by the termwise Hom equivalence.
- The ordinary r and s are the published `Etale.lowerStar` and `ProEtale.lowerStar`.
  `lowerStarCompComparisonLowerStarIso` is precisely δ, whose defining site
  isomorphism has identity components on the base-changed schemes and arrows.
  `comparisonResolutionRestriction` is r(h) followed by δ inverse, i.e. k.
  `comparisonResolutionTranspose` is the inverse comparison Hom equivalence on k,
  i.e. d. Both are chain maps constructed with the published termwise adjunction.
- The first conjunct is the requested ordinary chain equality: the termwise inverse
  of `comparisonUpperStarCompUpperStarIso` is a⁰; then p(d), then the ordinary
  pro-etale counit. The right side is A_U of the ordinary etale counit, then t.
- `comparisonResolutionIso` is the canonical resolution identification: the derived
  functor's comparison unit on the injective complex followed by the derived inverse
  of the augmentation. `comparisonResolutionEtaleIso` specializes it to i.
  `comparisonResolutionProEtaleIso` specializes it to `A_U(i) ≫ t` and composes
  the specified exact-localization factor `mapDerivedCategoryPlusFactorsh` inverse.
  No isomorphism is assumed as extra data. Termwise injectivity supplies the first
  invertibility; quasi-isomorphism supplies the second, via the homotopy localization.
- `comparisonResolutionDerivedMap` explicitly conjugates localized d by these two
  maps, inserting `A_V.mapDerivedCategoryPlusFactorsh` to identify its source.
  The second conjunct identifies this particular map with
  `fixedComparisonDirectImageMatePlus Λ f` at Q(F[0]).
- The third conjunct applies the specified derived pro-etale Hom equivalence inverse
  to that same map. Its right side is `fixedComparisonPullbackPlus` inverse followed
  by A_U of the specified derived etale counit, exactly the claimed transpose.
- The final conjunct quantifies over every `n : ℤ` and every section z of C at
  `⊤_ V.Etale`. The first equation is k(z)=h(z); the second evaluates d on the
  comparison unit image of z and equates it with h(z). The h evaluation is on
  `f.Etale.obj (⊤_ V.Etale)`, the chosen terminal base change, canonically U.
  Both equations use the same z, with no cycle condition. Evaluating J on this
  chosen terminal object avoids pretending the chosen fibre product is literally U.
- No hypothesis asserts preservation of injectives by either comparison functor.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, the `Sheaf … (ModuleCat Λ)` encoding;
  Mathlib `DerivedCategory.Plus`, `CochainComplex.Plus`, `CochainComplex.IsKInjective`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategoryPlus`, `finiteCoefficientRealization` and its
  equivalence identify the ring-sheaf presentation with this fixed-module presentation.
  They are not a second definition of the six-functor coefficient category.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and its fixed-module specialization are the same
  Kan-extension/sheafification adjunction as `comparisonAdjunction` used here.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`;
  `Etale.rightDerivedLowerStarPlus` is the published bounded derived direct image.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the finite
  coefficient operations; here the published fixed-module `ProEtale.upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction` and their derived adjunctions are used.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  the support-prefixed coefficient pullback and direct-image comparisons are the
  same canonical conjugate as `comparisonUpperStarCompUpperStarIso` inverse and
  `lowerStarCompComparisonLowerStarIso`, used in the statement and definitions.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `fixedComparisonDirectImageMatePlus_counit` give the specified normalized derived map.
- Mathlib `CategoryTheory.mateEquiv`, `Adjunction.comp`,
  `unit_conjugateEquiv_symm` provide the mate/composite normalization.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`:
  `Adjunction.mapHomologicalComplex`, `Adjunction.mapHomotopyCategory` supply the
  chain and homotopy adjunctions, with the published ordinary units and counits.
- Proof-dependency modules are imported non-publicly for stage 3: the exact inverse
  image, constant-ring comparison, comparison exactness, ringed-site K-injective
  existence, K-injective total derived, and general pre-derived adjunction modules.
  Their theorems are the node's recorded proof plan, not additional hypotheses.

Edge cases checked mathematically: empty U or V, zero coefficient ring, zero sheaf,
identity f, negative degrees (zero terms of the nonnegative resolutions), degree zero,
and arbitrary nonclosed terminal sections. No characteristic restriction, nonemptiness,
or restriction to a chosen injective resolution occurs. The orientation of δ is fixed
by its inverse in k; both ordinary and derived transpose equations have correct domains.

Searches actually run:

- `msearch.py … leanfinder`: “The restriction transpose chain map on injective
  resolutions represents the canonical etale to proetale derived direct image
  comparison and has the counit mate formula.” Eight hits, including
  `InjectiveResolution.rightDerived_app_eq`, `toRightDerivedZero_eq`, and resolution
  naturality lemmas; no site-specific chain/derived/terminal-section statement.
- `msearch.py … loogle 'CategoryTheory.Adjunction, "mapHomologicalComplex"'`:
  zero hits.
- `msearch.py … grep 'rightDerivedFunctorPlusUnit|rightDerivedFunctorPlusFactors'
  CategoryTheory`: zero hits in the queried Mathlib subtree; the appropriate generic
  derived comparison is in Mathlib/Algebra/Homology and was read directly afterward.
- `rg` on Mathlib and project homology files found `Functor.mapCochainComplexPlus`,
  `DerivedCategory.Plus.Q`, `rightDerivedFunctorPlusUnit`, and
  `mapDerivedCategoryPlusFactorsh`, all used instead of redefining their notions.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `resolutionMate`, `resolution_mate`, and `restrictionTranspose`: no hits.
  Concept searches located the existing FixedComparisonDirectImageMate and
  ProEtaleDirectImageMateCompatibility files. Neither states the supplied-resolution
  restriction transpose plus the degreewise terminal-section formulas of this node.

No statement correction or disputed statement. The blueprint opening paragraph was
read, as were the node's seven proof steps and its statement dependencies.

## Second reading by NH

Self-check only: the dispatcher explicitly forbids starting other agents; independent
review is performed by the maintainer after delivery. I reread the node with the final
signature. It retains the finite commutative ring, qcqs map, arbitrary sheaf and both
specified nonnegative injective K-injective resolutions. Each of the chain, derived-mate,
derived-transpose and two section clauses appears as a conjunct. I checked that the
resolution maps use i and `A_U(i) ≫ t`, rather than arbitrary isomorphisms. The terminal
base change is evaluated explicitly, using the same section z on both sides.
During elaboration I replaced an unavailable localization instance for Plus.Q by
localizing the quasi-isomorphism through Plus.Qh, and supplied source/target objects
explicitly; these repair elaboration and do not change any mathematical assertion.

## Returned-delivery repair

Maintainer point L at immutable head `e56170a8f46a`: the module duplicated
`AlgebraicGeometry.ProEtale.comparisonResolutionSingle`, already owned by
`Sheaf.Paper.ComparisonGlobalResolutionModel`. Removed the local definition and
its entry from `lean.declarations`; publicly imported the existing owning module.
The existing helper has implicit coefficient ring Λ, so all uses now read
`comparisonResolutionSingle F`. Both definitions have the identical underlying
`CochainComplex.singleFunctor` construction and boundedness witness at zero.
No helper was renamed, no second copy remains, and no mathematical hypothesis or
conclusion changed. The saved packet's initial dry run passed, but that did not
resolve the independently reported cross-module collision; this repair does.

Self-check: reread the existing helper's complete signature, docstring and body,
and the final theorem. F[0] still uses the same sheaf F over U and the same
`ModuleCat.{u + 1} Λ`; the augmentation i and all localized source objects now
refer to that one published helper. All four conjuncts (chain identity, derived
mate, derived transpose, and the pair of section equations) remain unchanged.
The live local checkout has no item module yet; all edits remain in the sandbox.
