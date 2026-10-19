## Worker report

The module `Sheaf.Paper.FiniteComparisonLocalizing` states
`AlgebraicGeometry.ProEtale.finiteComparisonLocalizing`. It also supplies the explicit
coefficient realization needed to apply the recorded internal-module constructibility
predicate to ordinary fixed-ring module sheaves. All definition data are actual
constructions. The two postponed theorems are the main statement and the exact-equivalence
property of that specified coefficient realization; the latter is the coefficient-transport
clause of the item's own statement and proof step 1, not an independent assumed bridge.

The node's hypotheses and clauses are rendered as follows.

* The standing field is `k`, with `Algebra (ZMod p) k` and
  `IsAlgClosure (ZMod p) k`, where `p` is prime. This represents the algebraic closure
  of any finite field of characteristic p: passing from F_q to its prime field does not
  change its algebraic closure. It does not enlarge the setting to arbitrary algebraically
  closed fields with transcendence. `X.Over (Spec (.of k))`, `LocallyOfFiniteType` and
  `QuasiCompact` on the structure morphism say precisely finite type over k.
* The coefficient prime is `ℓ`, with `Fact ℓ.Prime` and `hℓ : ℓ ≠ p`.
  `B` is a finite commutative discrete topological ring, with
  `hB : ∃ n : ℕ, (ℓ : B)^n = 0`. Ordinary site coefficients are `ULift B` in
  `Type (u+1)`, matching the existing finite-discrete ring-identification interfaces.
  A finite ring has a small representative; the lift only supplies the project's
  coefficient universe, and imposes neither nontriviality nor a choice of cardinality.
* Unbounded ordinary module-sheaf derived categories are `Etale.DerivedCategoryModule`
  and `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat (ULift B)))`.
  The comparison is exactly `(comparisonUpperStar (ModuleCat (ULift B)) X).
  mapDerivedCategory`, not a freely chosen functor.
* `eR` is an explicitly supplied monoidal ring identification of the exact type provided
  by `Profinite.finiteDiscreteCondensedRing_constant`. For every such identification,
  `finiteDiscreteSchemeRingIso B X eR` is the recorded canonical pullback to X.
  `finiteComparisonPresheaf` uses the existing `ordinaryAction` to internalize the
  given sectionwise action, with its actual unit and associativity laws; `finiteComparisonConstantRealization` applies
  monoidal sheafification; `finiteComparisonRealization` then restricts along the inverse
  scheme-ring isomorphism. Thus its action, and every linear map, is specified by the
  actual scalar/sheafification construction, rather than chosen from an existence theorem.
* `finiteComparisonEtaleGenerators` is the intersection of the recorded
  `Etale.DerivedCategory.isBoundedConstructible` and the existing
  `DerivedCategory.finiteTorAmplitude`. The latter quantifies over every sheaf in
  degree zero, with a single interval for all test sheaves. On the pro-etale side,
  `finiteComparisonProEtaleGenerators` uses exactly
  `constantModelBoundedConstructible (Profinite.continuousMapRingObj B) X` intersected
  with that same internal derived Tor-amplitude predicate, pulled back by the specified
  coefficient realization. No etale-origin replacement for pro-etale constructibility
  is used.
* Both `finiteComparisonEtaleClosure` and `finiteComparisonProEtaleClosure` use the
  recorded generic `CategoryTheory.localizingClosure`, the intersection of full replete
  triangulated sum-closed properties. All full categories have all ambient morphisms.
* The existential `hpres` states preservation of closure objects. The canonical
  `ObjectProperty.lift` of the specified comparison then has `IsEquivalence`.
  The triangle clause is exactness using the ambient distinguished triangles and
  the comparison's canonical shift commutation. The cofan clause quantifies over `I : Type (u+2)`, the ambient object's universe,
  and every ambient colimit cofan, exactly as the recorded localizing convention does.
  It states membership of its vertex in the closure and the colimit property of its image;
  it includes empty sums and does not assume the existence of larger coproducts.
* For each finite-type k-morphism `g`, the two clauses assert `IsIso` of the exact
  `unboundedDirectImagePullbackIso` component on an etale closure input on Y, and of
  `unboundedDirectImageComparisonMap` on an etale closure input on X. Their targets
  stay in the ambient derived categories. No stability of `Rg_*` is presumed.
* For an open k-immersion `j`, `finiteComparisonOpenIso` is obtained by localizing the
  existing sheaf-level `openImmersionLowerShriekComparisonUpperStarIso` and inserting
  only the canonical derived-composition isomorphisms. Its component on each closure
  input is asserted invertible.
* A chosen compactification is given by its open map `j : X ⟶ P` and proper map
  `r : P ⟶ Y`, all over k with P and Y finite type. Its composite is the morphism
  being compactified; no existence or independence assertion is added. The stipulated
  `Rf_! = Rr_* j_!` comparison is the explicit composite
  `finiteComparisonCompactSupportMap`: alpha at `j_! K`, followed by `Rr_*` of the open
  comparison. The final clause asserts invertibility of exactly this composite.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: read
  `finiteCoefficientModulePresheaf`, `FiniteCoefficientModules`, and the recorded finite
  module comparison. The ordinary module sheaves and `comparisonUpperStar` used here
  are exactly its fixed-ring source and its specified first comparison functor. The extra
  realization here lands in internal condensed modules, as the constructibility record
  requires, instead of the ringed-site module encoding.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`
  and `Scheme.proEtaleSiteComparisonModules`; the fixed-ring inverse image and adjunction
  are the existing `comparisonUpperStar` and comparison adjunction.
* The derived-category record names `WeilConjectures.AlgebraicGeometry.DerivedCategories`;
  its usable `Etale.DerivedCategoryModule` comes from the already imported coefficient
  framework. The side `Sheaf.AlgebraicGeometry.DerivedCategories` re-exports this same
  category, so no duplicate upstream torsion-cohomology declaration is imported.
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` (bounded cohomology and the recorded
  finite-value constructible sheaves).
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, built from `IsConstantModelConstructible` and
  `HasFiniteConstantLocalModel`. `Sheaf.Paper.LocalizingClosure`:
  `CategoryTheory.localizingClosure` and `IsLocalizingSubcategory`.
* `Sheaf.Paper.FiniteDiscreteCondensedRing`:
  `Profinite.finiteDiscreteCondensedRing_constant`;
  `Sheaf.Paper.FiniteDiscreteSchemeRing`: `finiteDiscreteSchemeRingIso` and its
  equality and monoid-morphism interfaces.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.ordinaryAction`, the tensor-linear form of the actual
  sectionwise scalar action. The generic `internalPresheafMod` was also read; its
  reconstructed section rings differ as structures from the fixed ordinary ring,
  so the specialization uses its existing action constructor directly. Its existing definition node is added to `stmt_deps`.
* `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison`:
  `unboundedDirectImagePullbackIso` and `unboundedDirectImageComparisonMap`.
  The former is the derived canonical pullback square; the latter is its precise
  inverse-image/direct-image adjunction mate, using the etale counit.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` via its public upstream imports.
* Mathlib `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`,
  `IsProper`, `ObjectProperty.lift`, and ambient triangles/cofans are used directly.
  Finite type is locally finite type plus quasi-compactness, and properness includes
  quasi-compactness via universal closedness.

Edge cases checked before writing: the zero coefficient ring, exponent n=0 (which forces
that ring), empty schemes and empty index sets, zero complexes, shifts in both directions,
identity morphisms and identity open immersions. There is no nonempty-scheme, nonzero-ring,
separatedness, properness-of-g, boundedness-of-input, or derived-completeness assumption.
The proper hypothesis occurs only on the chosen compactification's proper factor.

Searches actually run via `msearch.py Q24 det-ctf-finite-comparison-localizing`:

* LeanFinder: `etale proetale comparison equivalence localizing closures constructible
  finite Tor amplitude`. Eight results were ring-map etaleness/localization facts;
  none stated the comparison of localizing closures.
* Loogle: `CategoryTheory.localizingClosure, CategoryTheory.Functor.IsEquivalence`.
  No hits; unknown identifier `CategoryTheory.localizingClosure` in Mathlib.
* Mathlib grep: `localizingClosure|IsLocalizingSubcategory` in `CategoryTheory`.
  No hits.
* LeanSearch: `etale proetale unbounded derived comparison localizing subcategory
  finite Tor constructible complexes`. Eight hits concerned the generic construction
  of derived categories, boundedness and ring-map etaleness, not this statement.
* `rg` of the upstream `WeilConjectures` tree for the node id and
  `finiteComparisonLocalizing` found no declaration. `rg` of `lean/Sheaf` for the
  localizing vocabulary found the existing `LocalizingClosure` and
  `CondensedConstantConstructibility` definitions, both reused. The proposed declaration
  names were also checked against `dag/lean_names_upstream.json` and both source trees.
* Focused searches located the existing internal/sectionwise module construction,
  so the realization uses the existing `ordinaryAction` constructor.

The initial compile exposed a live proof-import collision: importing
`Sheaf.AlgebraicGeometry.UnboundedSiteComparison` pulls in
`ComparisonGlobalCohomology`, whose import of the older pro-etale derived lower-shriek
module collides with `rightDerivedLowerShriekOfCompactification` from the finite-coefficient
module. The prescribed wrapper labelled this a stale-live infrastructure retry.
The unused proof-only import was omitted; the exact dependency theorem remains named in
the proof docstring. All interfaces actually used by the statement are imported.
The other compiler repairs concerned explicit coefficient universes, the scalar-action
instance annotations, and namespace/line-break syntax; none changed the mathematical
statement. Final `scompile.py Q24 det-ctf-finite-comparison-localizing` succeeded with no
errors or warnings, compiling the sandbox in 7.5 seconds and the final library module
in 6.8 seconds. The node signature is verbatim and only `lean` plus the added landed
internal-module dependency differ from the base node. `deliver2.py Q24 det-ctf-finite-comparison-localizing --no-push` then printed
`OK (dry run)`: the complete delivery passed the server preflight and per-file compile.

## Second reading by Q24

The dispatcher explicitly prohibits starting another agent. This section records a second
pass by this worker, not a claim of an independent review; the maintainer's independent
review remains the delivery review.

With the node and module open, checked the finite-type structure-map hypotheses; the
prime inequality and coefficient exponent; ordinary unbounded source and target; use of
actual coefficient transport; bounded constructibility and uniform Tor test interval on
both sites; the same intersection convention for both closures; the functor specified by
`ObjectProperty.lift`; ambient triangle exactness; closure under and preservation of every existing ambient
sum, using the ambient object universe and including the empty sum; both directions of the pullback square; the direct-image
mate with its counit; exact termwise open comparison; and the precise compactification
composite. No stability theorem or arbitrary natural isomorphism has been substituted.
All helper declarations describe constructions or properties present in this same node's
coefficient and operation clauses. No source correction or disputed statement is needed.
