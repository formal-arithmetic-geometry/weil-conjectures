## Worker report

The module `Sheaf.CategoryTheory.SimplicialInversionProductParameter` states HTT
Lemma A.3.5.14, using the published simplicial inversion interface. The one
postponed theorem is
`CategoryTheory.SimplicialInversion.simplicial_inversion_product_parameter`.
All other declarations are constructions or predicates with actual data.
No statement correction, disputed statement, new node, or dependency repair is needed.

Clause-by-clause correspondence:

- Small simplicial categories and their vertex arrows are `CoherentNerve.SCat.{u}`
  and `underlying C`; arbitrary markings are the dependency's `Pair.marked`.
  `P : Pair.{u}` simultaneously binds C and its set W. There is no restriction
  that W contain identities, be saturated, or be closed under composition.
- The cartesian product is exactly the existing `SSet.MarkedCone.productIndex`
  with `productEnrichment`: actual pairs of objects, products of mapping
  simplicial sets, and coordinatewise identities and composition. `productMap`
  acts as `(f.obj, g.obj)` and `f.map ⊗ₘ g.map`, and `product` packages these
  maps as a functor. It does not choose any alternative product category.
- `productPair P D` has exactly W_D. The existential binds a marked arrow w
  with its endpoints and an object d; endpoint equalities and `HEq` require
  the vertex of the product arrow to equal `(w, 𝟙 d)`. `HEq` only transports
  the endpoints. In particular it includes neither all arrows with invertible
  second coordinate nor a saturated replacement of W_D.
- `q : P.category ⟶ L` and `k : (productPair P D).category ⟶ K` are the two
  localization units. `MappingProperty` is the recorded dependency's
  characterization of the derived pushout under its source. Its theorem
  supplies this property for every `LocalizationPresentation B P q` and
  characterizes it uniquely under C. Quantifying over these characterized
  units is independent of the choice of Bergner model structure or pushout
  representatives; it adds no mathematical assumption to the node's units.
- `ProductDescent` is a functor on the existing `BergnerHomotopyCategory` with
  a natural comparison isomorphism against the strict enriched product and
  the existing localization functor. Its `map` transports the derived
  product of arrows to the actual product objects. All its structure is
  existential in the theorem, rather than assumed of the input categories.
- `ProductComparison` asserts a unique comparison class r with the defining
  equation `Q.map k ≫ r = Q.map (productMap q (𝟙 D))`. The target is precisely
  `Q.obj (productIndex L D)`, and its source is `Q.obj K`. `IsIso r` is the
  requested isomorphism in h sCat. Uniqueness also follows from the mapping
  property's injectivity and ensures that the map is induced by q × 1_D.
- The last clause of `ProductComparison` quantifies over every three-arrow
  representative `K ← A → T ← L×D`, with DK equivalences as outside arrows,
  and requires the middle arrow to be a DK equivalence. The represented-class
  equality is explicit. This includes every actual strict representative
  by taking both outside arrows to be identities, and also representatives
  made using cofibrant and fibrant replacements. These are the same
  three-arrow conventions used in the dependency's `InvertsMarked`.
- `ProductNaturality E` quantifies over arbitrary marking-preserving enriched
  functors `f : P ⟶ P'` and arbitrary `g : D ⟶ D'`. The maps a and b are the
  induced localization maps, fixed by their explicit unit equations; r and
  r' are fixed by the comparison equations. Its conclusion
  `r ≫ E.map a (Q.map g) = b ≫ r'` is the naturality square in both variables.
  The dependency already states induced-map existence, identity and composition
  compatibility. No global choice of localization objects or inverses is made.
- There are no fibrancy, cofibrancy, saturation, or nonemptiness hypotheses.
  The universe u is explicitly bound, and can be any containing universe for
  all the displayed small simplicial categories. No implicit variables occur.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`:
  `SimplicialInversion.MappingProperty`, `Uniqueness`, `InducedMaps`,
  `CompositionCompatibility`, and `simplicial_inversion_universal_property`.
  Read its full statement, its proof docstring, and its representative
  inversion predicates. It imports the existing `Pair`, `PairHom`, and
  `LocalizationPresentation` from `SimplicialLocalizationComparisonCalculus`.
- `Sheaf.CategoryTheory.SimplicialFullyFaithfulHomotopyImage`:
  `bergnerWeakEquivalences`, `BergnerHomotopyCategory`,
  `bergnerHomotopyFunctor` (available through the dependency).
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`:
  `SSet.MarkedCone.productEnrichment` and `productIndex`, whose full
  constructions were read. Only these definitions are reused; its theorem
  is not used as an assumption or proof input. Adding its theorem node as
  a mathematical dependency would create the already audited path
  marked-cone-external-product → coherent-nerve-comparison →
  rigidification-equivalence-detection → pinched-rigidification-resolution →
  right-straightening-fiber-comparison → contravariant-slice-model →
  unstraightening-homotopy-descent → simplicial-localization-comparison-calculus
  → this item. Reusing its definition does not cite that downstream theorem.
  No second product definition or copy was introduced.
- The already recorded proof dependencies `RealizationFiniteLimits` and
  `SimplicialProjectiveModelCalculus` are non-public proof imports. The two
  proof-only nodes `lem-coef-simplicial-derived-exponential` and
  `lem-coef-simplicial-model-target-test` have no Lean record in the current
  DAG; their imports are deferred, as allowed for unstated proof inputs.
  They are not missing notions required to type the statement.

Source check: opened the current HTT PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, printed p.896 (PDF page
913 zero-based), Lemma A.3.5.14 and its displayed four bijections. The lemma
is exactly the enriched tensor/product localization comparison; for cartesian
simplicial sets this is the product used here. The proof docstring follows all
six steps of this node's expanded proof, including the actual restriction map,
essential surjectivity, and naturality, rather than just an abstract bijection.

Edge cases checked:

- D empty: product objects and W_D are empty; all defining formulas and the
  representative/naturality quantifiers still type, with no Nonempty binder.
- C empty: W and C×D are empty, again without an excluded case.
- W empty: `productPair` has no marked arrows, so these are the corresponding
  unmarked localizations; no identity marking is silently introduced.
- D terminal: W_D is exactly the original marking under the product with the
  terminal category; the comparison is the usual localization unit comparison.
- Marked identities, repeated endpoints, and nontrivial automorphisms: the
  product marking retains the actual identity at d; no strict inverse in C
  or D is required, and inversion is in the component category.
- Non-Kan mapping sets and arbitrary small universes: no local Kan or fixed
  finite/countable size restriction occurs.
- Strict representatives are included by identity outside arrows; replacements
  are included by arbitrary DK outside arrows in the displayed equality.

Searches before writing:

1. `msearch.py ... leanfinder "derived localization of simplicial categories
   commutes with cartesian product inverting marked arrows"`: 8 hits. These
   concern SSet.hoFunctor preserving products and ordinary localization
   products, and do not state derived inversion of simplicial categories.
2. `msearch.py ... loogle "CategoryTheory.Functor.IsLocalization.prod,
   EnrichedCategory"`: no hits, unknown identifier EnrichedCategory.
   Read `Mathlib/CategoryTheory/Localization/Prod.lean` separately: its
   theorem is ordinary category localization, with identity-containing
   morphism properties; it is not this homotopical statement.
3. `msearch.py ... grep "Simplicial.*Product|cartesian product|SCat.*product"
   CategoryTheory`: 22 hits, all ordinary products or simplicial objects in
   formal coproduct categories, no matching theorem.
4. `rg` in upstream `WeilConjectures`, Mathlib's Enriched and SimplicialCategory
   directories, `dag/lean_names_upstream.json`, and the project's `lean/Sheaf`
   for SimplicialInversion, productComparison, productParameter, SCat/product,
   productIndex/productEnrichment: no theorem match. The project search found
   the reusable exact product construction in MarkedConeExternalProduct.
5. `grep -rn` of the exact item id in upstream `WeilConjectures`: no match.
   Name searches for the proposed public declarations found no collisions.
6. DAG searches for simplicial products and `tools/blueprint_refs.py search
   'simplicial cartesian product'`: no independent definition node; the latter
   returned 0 blueprint nodes. The existing product construction is reused
   directly, so no new definition node was needed.

Validation: `scompile.py Q70 lem-coef-simplicial-inversion-product-parameter
<module>` compiles both sandbox and installed-path probes cleanly with no
warnings, within the required 60-second per-file limit. Initial elaboration
experiments established the precise ForgetEnrichment arrow types; final
source has no probes or scratch declarations. All source lines are at most
100 characters. The node copy changes only its `lean` record.

## Second reading by Q70

No second reading by a separate worker: the dispatched brief forbids starting
other agents and says that the maintainer's independent review reads the
delivery. A final in-session check matched every binder and clause against
the node and the actual source. It checked in particular the exact W_D
marking, the unit-triangle characterization of r, arbitrary replacement
representatives, both variables of naturality, all empty cases, and that
ProductDescent is supplied by the theorem rather than an added hypothesis.
The earlier unused simp arguments and long lines were removed and the final
module was recompiled cleanly.
