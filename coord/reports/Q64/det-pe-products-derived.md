## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` states
`AlgebraicGeometry.Scheme.ProEt.products_derived`, with proof `sorry`.
The natural-language node is unchanged; no new nodes or dependency statements are written.

Hypotheses and clauses, matched individually:

- The scheme is `X : Scheme.{t}` and its small pro-etale site is
  `Scheme.ProEt` with `topology X`, exactly the recorded Mathlib interface of
  def-weil-pbc-small-proetale-site. The site retains object universe t+1 and
  morphism universe t.
- An arbitrary sheaf of rings is `R : Sheaf (topology X) RingCat.{max u (t+1)}`.
  There is no commutativity, constant-coefficient, finiteness or characteristic
  condition. The coefficient/module universe contains the indexing set and site;
  u remains arbitrary, so larger coefficient universes and arbitrary index sets
  are included by choosing the common size bound. No site universe is enlarged.
- The arbitrary set, in the chosen common size bound, is `I : Type u`, without Nonempty,
  Countable or Finite.
- The unbounded family is
  `K : I → CochainComplex (ringedSiteModules.{max u (t+1)} R) ℤ`.
  `ringedSiteModules` is the dependency's transparent abbreviation of
  `SheafOfModules`. No replacement category or Abelian structure is chosen.
- `HasDerivedCategory.{v}` chooses the localization and morphism universe v,
  following def-weil-abstract-derived-category; no equality of site universes is
  imposed.
- The first conjunct is `Nonempty (IsLimit
  (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor K))))`.
  This asserts the full universal property with the actual localized projections,
  including uniqueness for maps from arbitrary derived objects.
- The second conjunct quantifies over every `p : ℤ` and asserts `IsIso
  (piComparison (HomologicalComplex.homologyFunctor ... (ComplexShape.up ℤ) p) K)`.
  Mathlib's piComparison has source H^p of the termwise product and target the
  product of H^p(K i), and its components are the cohomology maps of the actual
  projections. This gives the requested canonical cohomology isomorphism.
- The third conjunct quantifies over every second family K' and every family of
  maps f. From `∀ i, QuasiIso (f i)` it concludes
  `QuasiIso (Limits.Pi.map f)`. This is the categorical product map, with its
  degreewise coordinate maps, rather than an arbitrary map between representatives.

Why the chosen complex product is termwise: in Mathlib's
`Algebra.Homology.HomologicalComplexLimits`, the `HasLimit` instance used by
`limit.cone (Discrete.functor K)` is constructed with `coneOfHasLimitEval`.
Its degree-n object is the limit of the evaluated discrete family, its
 differential is `limMap` of the differentials, and the projections in every
 degree are `limit.π`. The differential and projections therefore are precisely
 the termwise ones in the node. The same Mathlib module makes evaluation preserve
 limits. Product existence comes from `SheafOfModules.hasLimitsOfSize` and
 `HomologicalComplex`'s degreewise `HasLimitsOfShape`; no product-existence
 hypothesis is added.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale: `AlgebraicGeometry.Scheme.ProEt` and
  `AlgebraicGeometry.Scheme.ProEt.topology`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- Mathlib.CategoryTheory.Limits.Shapes.Products: `piObj`, `Pi.π`, `Pi.lift`,
  `Limits.Pi.map`, `piComparison`, and `IsLimit`/`Fan`.
- Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex and QuasiIso:
  `HomologicalComplex.homologyFunctor`, `QuasiIso`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits and HomologicalComplexLimits:
  the existing module-sheaf and degreewise complex product constructions.
- Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit supplies the
  already-published `AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify` and
  `surjectiveTower_wEqualsLocallyBijective` instances at larger coefficient
  universes. Their full definitions were read: both transport along the small
  model, retaining the original small site. They supply Mathlib's canonical
  Abelian instance, with no auxiliary mathematical hypothesis.

Proof-dependency imports retain the five-step plan for stage 3:
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact` (`Scheme.ProEt.products_exact`),
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
(`SheafOfModules.isGrothendieckAbelian`),
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
(`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`),
and `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`
(`CochainComplex.termwise_product_isKInjective_and_isLimit`). The last module
was read through `scompile.py --source`, as its recorded file is absent from the
stale shared source copy. The exact-products dependency is likewise published:
its full current source was confirmed by `scompile.py --source
Sheaf.AlgebraicGeometry.ProEtaleProductsExact`; it is not an unstated prerequisite.
The size-convention node is metatheoretic and has no module.

Sources read: the current main-20261015 blueprint statement and complete proof
for det-pe-products-derived, the item's five proof steps, all four statement
 dependency nodes, and every recorded declaration's full signature/docstring.
The theorem docstring follows all five steps, including naturality, the product
of quasi-isomorphisms, K-injective resolutions, and transfer using actual
projection squares.

Edge cases: the empty product is the zero/terminal complex; the localized cone
is terminal, the cohomology comparison is zero to zero, and the product of the
empty map family is an isomorphism. Singleton products recover the original
complex and cohomology maps. Zero complexes and the zero ring give zero
throughout. Unbounded families with no common cohomological bound remain
allowed. Noncommutative ring sheaves use the same left-module category.

Searches performed through msearch.py for Q64 and this item (searches.jsonl
is the tool log): LeanFinder query "products of complexes in derived category
termwise product cohomology commutes products quasi-isomorphism" returned eight
hits, chiefly DerivedCategory.Q and homologyFunctorFactors, none the full item.
Loogle query "DerivedCategory.isLimitFanMkQObj, HomologicalComplex.isLimitFanHomology"
returned zero hits (unknown upstream identifier). Mathlib grep queries
"derivedCategory.*product|isLimitFanMkQObj" and "piComparison|quasiIso_limMap"
returned zero hits in the requested homology subdirectories. LeanSearch query
"For complexes of sheaves of modules on the pro-etale site termwise products
are products in the derived category and commute with cohomology" returned
ordinary sheaf products, SheafOfModules.hasLimit and tensor-complex APIs,
not the complete statement. Direct rg searches of upstream WeilConjectures,
lean/Sheaf, and dag/lean_names_upstream.json for the item tag and products_derived
found no existing declaration of this item.

Further direct source searches found upstream generic tools
`DerivedCategory.isLimitFanMkQObj`, `HomologicalComplex.isLimitFanHomology`,
and `HomologicalComplex.quasiIso_limMap`. Their full signatures/docstrings were
read. They assume abstract exact products and K-injective resolutions; none
states all three clauses for arbitrary pro-etale ring sheaves without these
extra hypotheses. The countable-only side theorem is also not the arbitrary
family statement. No duplicate notion is introduced.

No STATEMENT-DISPUTED issue, statement correction, or new node is needed.
Validation uses only the prescribed single-file scompile.py wrapper and the
prescribed deliver2.py --no-push dry run. No global build or direct git command
was run, and no shared/library source was edited.

## Second reading by Q64

I reread the node statement, its Stacks source, every recorded statement dependency, and the
Lean declaration independently.

- **Objects.** The node's scheme (X), small pro-etale site (X_{\mathrm{proet}}), sheaf of
  (possibly noncommutative) rings \(\mathcal R\), index set \(I\), and family of unbounded
  complexes \((K_i)\) are rendered by `X : Scheme.{t}`, `topology X`,
  `R : Sheaf (topology X) RingCat.{max u (t + 1)}`, `I : Type u`, and
  `K : I → CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ`. The module category is
  exactly the recorded transparent `CategoryTheory.ringedSiteModules`, not a private copy.
  The `[HasDerivedCategory.{v} ...]` binder supplies the chosen derived localization required
  to express (D(X_{\mathrm{proet}},\mathcal R)); it adds no mathematical restriction.
- **Product clause.** The node's assertion that the termwise product is a product in the
  derived category is rendered by
  `Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor K))))`.
  `limit.cone` is the homological-complex limit built degreewise by
  `HomologicalComplex.coneOfHasLimitEval`, so its object, differential, and projections are
  the termwise product construction. `IsLimit` retains the full universal property and its
  uniqueness for every derived object.
- **Cohomology clause.** The node's assertion for every (p\in\mathbb Z) is rendered by
  `∀ p : ℤ, IsIso (piComparison (HomologicalComplex.homologyFunctor ... p) K)`. The
  comparison is the canonical map induced by the product projections from cohomology of the
  product to the product of cohomologies, exactly the node's (H^p(\prod_iK_i)\cong
  \prod_iH^p(K_i)).
- **Quasi-isomorphism clause.** The node's universally quantified second family and component
  maps are rendered by `K' : I → CochainComplex ...`, `f : ∀ i, K i ⟶ K' i`, and
  `(∀ i, QuasiIso (f i)) → QuasiIso (Limits.Pi.map f)`. This is the canonical categorical
  product map, with no extra boundedness, finiteness, commutativity, characteristic, or
  nonemptiness hypothesis.

The source check used the blueprint's complete five-step proof and Stacks `injectives.tex`:
Tag 079P (`theorem-K-injective-embedding-grothendieck`) gives K-injective resolutions in a
Grothendieck abelian category, while the adjacent `lemma-derived-products` gives the derived
product construction. The blueprint's exact-products argument supplies the stronger
termwise-product conclusion and the cohomology and quasi-isomorphism clauses. The Lean
statement has precisely the source's three conclusions and does not import a bounded or
countable-family assumption.

Edge cases checked: `I` may be empty (the categorical product is terminal/zero in the additive
complex category and the empty product map is the canonical isomorphism); `I` may be a
singleton; complexes may be zero or unbounded in both directions; (p=0) and arbitrary
(p\in\mathbb Z) are covered; the site or scheme may be empty; and no characteristic or
commutativity condition is imposed. The common universe convention is the one used by the
recorded small-site and exact-products interfaces, and the separate derived-category universe
`v` is unconstrained.

I repeated the existing-definition searches with `msearch.py` (LeanFinder, Loogle, and grep),
`rg` over `WeilConjectures/`, the repository's `lean/Sheaf/`, and
`dag/lean_names_upstream.json`, including searches for `products_derived`, derived products,
termwise complex products, `piComparison`, and K-injective products. The only matches were
generic ingredients (`DerivedCategory`, `piComparison`, K-injective and homological-complex
limit APIs); no declaration states this complete pro-etale theorem. No new definition node or
dependency repair is needed.

Mismatches found: none. I did not alter the node's natural-language statement, its dependency
list, or the Lean signature. The copied node `lean.statement` remains byte-for-byte equal to the
compiled theorem signature. The prescribed `scompile.py` check passes with only the expected
`sorry` warning.
