## Worker report

The module `Sheaf.Paper.ProductTensorTestBounds` states
`SheafOfModules.product_tensor_test_bounds`, with its entire proof `sorry`.
No mathematical statement, dependency list, or proof plan in the DAG changed.
All four helper declarations contain real data and carry this node's source and blueprint tag.
No new node or dependency module is needed.

Hypotheses and objects, matched clause by clause:

- The global ringed site is `{C : Type u} [Category.{v} C]`, `J`, and
  `R : Sheaf J CommRingCat.{r}`. Component sites are `Ci`, `Ji`, and `Ri`.
  `[EssentiallySmall.{r} C]` and the corresponding component instances express
  smallness relative to the module universe. Object, morphism, coefficient, and
  derived-localization universes are independent. The sites can thus have object
  universe t+1 and morphism universe t, as on the small pro-etale site.
- `{I : Type t} [hI : Finite I]`, retained in the theorem by `include hI`, is the
  finite index set. There is no Nonempty assumption or selected component.
- `productBoundsModules R` is only an abbreviation of the recorded
  `CategoryTheory.ringedSiteModules.{r}` after forgetting coefficient commutativity;
  it introduces no second category or Abelian instance. The ordinary Mathlib
  Abelian instance comes from essential smallness. The two `HasDerivedCategory`
  binders specify the allowed localization sizes, without imposing their equality.
- `e : productBoundsModules R ≌ (∀ i, productBoundsModules (Ri i))`
  supplies exactly the equivalence r and the specified quasi-inverse G=`e.inverse`.
  `productBoundsRestriction e i` is `e.functor ⋙ Pi.eval _ i`, the actual coordinate
  functor r_i. Its `Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`
  instances state additive exactness coordinatewise. These imply additive exactness
  of the product functor and its inverse: limits and colimits are pointwise and
  equivalences preserve them, while additivity transfers across the unit/counit.
  No Abelian structure on a product is chosen or assumed.
- `productBoundsInsertion e i N` applies the specified inverse to the tuple whose
  j-entry is transported N when i=j and the zero object otherwise. Its definition
  uses an equality case split, not a chosen preimage or an arbitrary lifting map.
- `productBoundsDerived J R Ji Ri e i` is exactly
  `(productBoundsRestriction e i).mapDerivedCategory`, the localization of
  degreewise restriction. The definition does not assume an unrelated derived functor.
- `hH` gives a natural isomorphism of functors
  `D_i ⋙ homologyFunctor _ m ≅ homologyFunctor _ m ⋙ r_i` for every i and integer m.
  `hT` gives a natural isomorphism of the two bifunctors
  `T ⋙ D_i ≅ (D_i.prod D_i) ⋙ T_i`. Nonempty is used only to assert existence of
  these specified natural comparisons, exactly as in the hypothesis; it never
  supplies arbitrary mathematical data.

Conclusion, in order:

- The first outer conjunct quantifies over every unbounded derived object K and
  all `a b : ℤ` with `a ≤ b`. Its first equivalence is precisely global cohomology
  vanishing outside `Set.Icc a b` iff the same vanishing for every component.
  Zero means `CategoryTheory.Limits.IsZero` of the actual cohomology sheaf.
- The second equivalence in that conjunct is global Tor amplitude iff component
  Tor amplitude, expanded rather than introducing a duplicate definition.
  Global tests quantify over EVERY `M : productBoundsModules R`; component tests
  quantify over EVERY i and EVERY `N : productBoundsModules (Ri i)`.
  Degree-zero objects are `(DerivedCategory.singleFunctor _ 0).obj M` (or N).
  Tensor is exactly `siteDerivedTensorIndependentCoefficients`, the recorded
  canonical K-flat tensor bifunctor. The upstream `DerivedCategory.torAmplitudeIn`
  requires a different derived monoidal interface; its test condition agrees with
  this expression, but cannot directly name the recorded site-tensor bifunctor.
- The next conjunct states `r_i(e_i N) ≅ N` and `IsZero (r_j(e_i N))` for j≠i.
  These are the node's unit/counit zero-insertion identifications.
- The next conjunct states the actual isomorphism in the component DERIVED CATEGORY
  `D_i(T(K,(e_i N)[0])) ≅ T_i(D_i K,N[0])`, for every component test N and K.
  It is not replaced by only per-degree comparisons.
- The final conjunct states that ANY zero derived object has both interval
  conditions for every ordered interval. There is no boundedness or constructibility
  hypothesis anywhere on K.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent alias for Mathlib `SheafOfModules`; Mathlib's existing category and
  Abelian structure are used.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and its actual localization functor.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its representative comparison
  `homologyFunctorFactors` (read in source).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, whose full signature
  and universal-property characterization were read. It retains independent site
  and coefficient universes and is determined by its K-flat representative comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, with its degreewise factorization
  and `mapDerivedCategorySingleFunctor` comparison, read in full.
- `Mathlib.CategoryTheory.Pi.Basic`: `CategoryTheory.Pi.eval`.
- All stated proof dependencies are imported (proof-only imports are plain):
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
  (`CochainComplex.IsKFlatIndependentCoefficients`),
  `Mathlib.Algebra.Homology.BifunctorShift` (`CochainComplex.mapBifunctor`), and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
  (`SheafOfModules.IsFlatOnSite`). The flatness and K-flat predicates were read.

Edge cases checked mathematically: for empty I, the equivalence with the empty
product forces every global module to be zero; component conditions are vacuous
and both global vanishing conditions hold. For K=0, the K-flat formula gives
zero tensor tests in every interval. Singleton I recovers invariance under the
specified equivalence. Intervals with a=b and negative endpoints are included;
zero insertion covers every component module, including zero. The statement
requires a≤b exactly as the source; no normalization or positivity is imposed.
No node fault or STATEMENT-DISPUTED issue was found.

Searches (actual logged results, see sandbox searches.jsonl):

- msearch leanfinder: “An exact tensor compatible equivalence with a product of
  module sheaf categories detects cohomology bounds and Tor amplitude intervals”;
  eight hits including `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `DerivedCategory.isGE_Q_obj_iff`, `DerivedCategory.isLE_Q_obj_iff`,
  `CategoryTheory.Tor`, and `Module.Flat.lTensor_shortComplex_exact`; no exact match.
- msearch loogle: `DerivedCategory, CategoryTheory.Equivalence`; zero hits.
- msearch grep: `torAmplitude|tor_amplitude|TorAmplitude`; zero Mathlib hits.
- msearch leansearch: “An exact tensor compatible equivalence with a finite product
  of module sheaf categories detects cohomological intervals and Tor amplitude”;
  eight ordinary module tensor hits (`TensorProduct.piRight`, `TensorProduct.piLeft`,
  `Algebra.TensorProduct.piRight`, `lTensorHomEquivHomLTensor`,
  `IsLocalization.moduleTensorEquiv`, `PiTensorProduct.dualDistribEquiv`,
  `homTensorHomEquiv`, `LinearEquiv.lTensor`); none states the theorem.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for product/tensor,
  Tor intervals and amplitude found specialized site and scheme Tor definitions
  and clopen decomposition results, not this abstract theorem. In particular,
  read `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`,
  `Sheaf.Paper.FiniteClopenDerivedDecomposition`, and
  `Sheaf.Paper.CohomologyTorInterval`: the first defines an existing monoidal Tor
  notion, the second assumes geometric clopen input, and the third derives a Tor
  interval from cohomology. None is this exact-product detection assertion.
- Direct rg for this node id in `lean/WeilConjectures` found no existing declaration;
  searches for each of the five proposed declaration names in both source roots
  and `dag/lean_names_upstream.json` found no collision.

Source checks: opened the current blueprint's def-pur-section-invariant.md
(final “invertible by co-smoothness”), the node's complete six-step proof, and
Stacks sites-cohomology.tex definition-tor-amplitude (Tag 08FZ). The latter tests
against every module sheaf and every degree outside the ordered interval, exactly
as rendered here. The theorem docstring includes all six proof steps with their
DAG citations. The example CompactObject module is now withdrawn; the extant
RingedSiteModules dependency supplies the module/header/public-section convention.

Validation: scompile.py compiled the final file successfully both as a sandbox
module and at its intended module path, with no errors or warnings. Every theorem
proof is sorry; definitions and abbreviations have concrete bodies. All universes
and variables are explicitly bound, and all lines are at most 100 characters.
The maintainer performs the independent review under the dispatch brief.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
