## Worker report

The module `Sheaf.Algebra.Homology.StrictCoefficientTensorDescent` states
`WeilConjectures.SemilinearSections.StrictCoefficientTensor.strictCoefficientTensorDescent`.
Its only postponed theorem has proof `sorry`. `Resolving`, `Scalar`, and `pure` have
complete data; `Descent` packages precisely the normalized strict descent assertion.
No coefficient map is assumed flat, surjective, or an epimorphism.

Hypothesis and clause correspondence:

- A site small relative to module sheaves: `{C : Type c} [Category.{v} C]
  [EssentiallySmall.{r} C] (J : GrothendieckTopology C)`. Site objects, arrows, and
  coefficients have independent universes. The existing small-site sheafification
  instances are used; no equality between site universes is imposed.
- The commutative ring sheaf is `R : Sheaf J CommRingCat.{r}`. The inverse sequence is
  `S : ℕ → Sheaf J CommRingCat.{r}`, `q : ∀ n, S (n+1) ⟶ S n`. Lean index zero is
  the paper's index one, so every paper index is included.
- The R-algebra structures are `a : ∀ n, R ⟶ S n`; their compatibility is exactly
  `ha : ∀ n, a (n+1) ≫ q n = a n` in the theorem.
- The strict category is the existing `SemilinearSections.Systems J S q`, module
  sheaves on the ringed sequence site. Its module restrictions are the semilinear
  transitions, and morphisms commute with them. Its inherited abelian structure and
  `evaluation_exact` give componentwise kernels, cokernels and cohomology.
- `Descent.ordinary` and its additive instance give the module tensor functor.
  `Descent.scalar n` is the recorded `DerivedChangeOfRingsCochainModel (a n)`.
  Its `obj_eq` and `map_eq` fix ordinary extension to `changeOfRings` and
  `changeOfRingsHom`. `level n` is a natural isomorphism to that actual extension,
  fixing chain-map actions, not just the object assignment.
- `ordinary.mapHomologicalComplex (.up ℤ)` is F on unbounded complexes, with
  differential `ordinary.map P.d`. Naturality of `level` identifies this with
  `d_P tensor 1`. `Functor.mapHomotopy ordinary` acts on each homotopy component
  by that same tensor functor. No arbitrary complex or homotopy functor is assumed.
- `pure` is the actual sheafification-unit section, transported along the dependency's
  object equality and multiplied by the target coefficient. The source tensor
  convention is coefficient tensor x, the symmetric version of the node's x tensor c.
- `transition_pure` prescribes every strict transition, not just adjacent maps: after
  `level`, it carries the pure section at m to the pure section at n with coefficient
  `coefficientMap J S q h`. This is the existing `Functor.ofOpSequence q` map and
  hence uses actual composites, including the identity, and no independently chosen
  composite-index morphisms.
- `Resolving` is the recorded K-flat predicate together with `∀ i, IsFlatOnSite (P.X i)`.
  `preserves` says exactly that quasi-isomorphisms between these complexes remain
  quasi-isomorphisms of strict-system complexes.
- `T : D J R ⥤ DS J S q` lands in the ordinary derived category of entire strict
  systems, not diagrams in separate derived categories. `triangulated` specifies
  its shift-commutation structure and exactness.
- `ε` is a natural transformation from localization then T to termwise ordinary
  tensor then localization. `computes` makes it an isomorphism on every resolving
  complex. Its naturality applies to chain maps; inverting denominator maps gives
  precisely roof naturality and independence of K-flat representative.
- `pointwise` and `universal` express the everywhere-defined left-derived universal
  pair. `unique` additionally asserts uniqueness for the specified resolving-class
  normalization itself, even for a second pair not assumed universal. Its equation
  is `α.hom.app (Q.obj P) ≫ ε'.app P = ε.app P`.
- `evaluation n : T ⋙ e J S q n ≅ (scalar n).T` gives the requested natural
  identification with derived scalar extension. `evaluation_normalized` fixes it by
  the two computation counits and the termwise level comparison. Thus the transition
  obtained from the existing `derivedTransition` is the localization of the specified
  strict transition, rather than an arbitrary level morphism. The formula and actual
  composites survive localization, including on inverse quasi-isomorphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`;
  the existing Grothendieck topology/sheaf presentation is retained.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through `SemilinearSections.res`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the retained sheafified tensor API.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, publicly retaining
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` (E, object/map equalities,
  K-flat invariance, T, counit, universal property and computation).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  through the transparent existing `SemilinearSections.Mod`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, through the existing D and DS.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- Added landed statement dependency `def-coef-semilinear-system-models`, module
  `Sheaf.Paper.SemilinearSystemModels`: `Systems`, `DS`, `Mod`, `D`, `hasDerived`,
  `evaluation`, `e`, `transition`, `derivedTransition`, `coefficientMap`, `res`,
  `extensionUnit`, and its canonical small-site sheafification instances.
- The stated proof dependencies are imported plainly: the K-flat resolution,
  resolving-class theorem, saturated quasi-isomorphism theorem, dense-subcategory
  right-fraction theorem, exact-functor derived construction and localization
  universal-property API. Homotopy triangulation is already publicly imported by
  the Mathlib derived-category construction.

Sources opened: `literature/stacks-project/sites-cohomology.tex`, labels
`lemma-K-flat-resolution`, `lemma-factor-through-K-flat`, `lemma-derived-base-change`;
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-def-sp-normalized-towers/`
`sk-def-sp-normalized-towers-reduction.proof.md`, Construction paragraph. The node
expands that paragraph's simultaneous strict tensor construction. No source-based
statement correction is needed.

Edge cases checked before writing: zero complexes and zero coefficient rings are
allowed; the site can be empty; arbitrary unbounded complexes are allowed; coefficient
maps can fail flatness and surjectivity. The natural-number shift loses no positive
index, and `m = n` is included in `transition_pure`. There are no geometric, Tor-bound,
Noetherian, dimension or constructibility assumptions. The coefficient universe may
be smaller than the displayed site universes provided the site's existing relative
essential-smallness witness is supplied. The derived Hom universe is the existing
canonical larger one `max c v (r+1)` on both the site and its sequence site.

Searches (2026-10-24):

- msearch LeanSearch, "Tensor functor from sheaf module complexes to strict
  coefficient systems descends via K-flat resolutions": 8 hits, Tor and flat tensor
  exactness results; none constructs this strict-system derived functor.
- msearch LeanFinder, "K-flat tensor extension to the derived category of strict
  semilinear systems of sheaf modules": 8 hits, flat tensor and Tor; no exact match.
- msearch Loogle, "SheafOfModules.restrictScalars, DerivedCategory.Q": 0 hits.
- msearch grep, "strict.*system|semilinear", Mathlib Algebra: 25 capped hits about
  ordinary semilinear linear maps; no strict derived tensor descent.
- rg of project Sheaf and WeilConjectures for strict systems, coefficient tensors,
  semilinear systems and StrictReduction found the generic semilinear-system model,
  specialized integral strict reduction and ordinary fixed-R tensor towers. The
  latter has a different target (fixed-ring module diagrams); the integral model
  requires a pro-etale coefficient field setup. Neither is this arbitrary-site,
  arbitrary-coefficient statement. Reuse the generic model rather than duplicate it.
- rg of WeilConjectures for this exact node id: no declaration. rg of Sheaf found
  only a proof-docstring citation in `PurSequenceKFlatComparisonShifts`.
- `tools/blueprint_refs.py search semilinear` and the DAG records were read; the
  existing `def-coef-semilinear-system-models` owns the needed strict category.
  No new definition node or dependency repair is required.
- The chosen namespace and theorem name were searched in Sheaf, WeilConjectures
  and `dag/lean_names_upstream.json`: no existing declaration.

Validation uses scompile.py only. The first compile identified under-applied
independent-universe flatness and scalar-model parameters; these were made explicit
without changing any mathematical hypothesis. No live source or tools were edited.

## Second reading by Q122

I reread the complete node and the completed module in this same worker session;
no other agent was started, as the dispatcher explicitly prohibits that. This is a
second pass, not a claim of an independent worker review; the maintainer's review
remains independent.

The initial interface omitted explicit localization universes on scalar models;
the `Scalar` abbreviation now names the exact dependency model with its canonical
source and target derived categories. Flatness now explicitly names all four
universes, so no coefficient/site equality is silently inferred. Every tensor level
is specified through the dependency's actual object/map equalities and a natural
comparison. The transition formula includes all pairs n ≤ m, not only adjacent
indices. The target is DS, not a functor category over D. The universal pair and the
extra `unique` field express the stronger normalization-specific uniqueness in the
node, while `evaluation_normalized` prevents arbitrary level isomorphisms. No clause
was weakened or discarded, and the theorem assumes only R-linearity of the given
coefficient transitions. No node fault or STATEMENT-DISPUTED issue was found.
