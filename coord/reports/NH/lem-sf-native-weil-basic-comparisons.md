## Worker report

`Sheaf.WeilSheaf.NativeBasicComparisons` states
`AlgebraicGeometry.nativeWeilBasicComparisons`, with one `sorry` and no new definitions.
The theorem is the conjunction of the five universally quantified assertions in the
node, using the actual upstream native operations. The node changes only in `lean`.
There are no new nodes, dependency repairs, or statement corrections.

### Hypotheses and clause correspondence

- The finite base field is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
  The prime is `(l : ℕ) [Fact l.Prime]`, and the different characteristic is
  `[Fact (ringChar k₀ ≠ l)]`. The coefficient field is the framework's
  `PadicAlgCl l`, already built into `ProEtaleWeilSheaf k₀ l S`.
- Each scheme is explicitly `Scheme.{u}` with its
  `[S.Over (Spec (CommRingCat.of k₀))]` structure and
  `[LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k₀))]` hypothesis.
  Every map is over this base through `f.IsOver`, `g.IsOver`, `j.IsOver`, or `i.IsOver`.
  There is no absolute separatedness, quasi-separatedness, or global quasi-compactness
  hypothesis on the schemes, and no morphism finiteness hypothesis in part (a).
- The first conjunct is part (a)'s composition: for `f : S ⟶ T` and `g : T ⟶ H`,
  `Nonempty ((lowerStar k₀ l (f ≫ g)).rightDerivedFunctor ≅
  (lowerStar k₀ l f).rightDerivedFunctor ⋙ (lowerStar k₀ l g).rightDerivedFunctor)`.
  Lean's left-to-right functor composition is precisely the paper's `Rg_* Rf_*`.
  The isomorphism is a natural isomorphism of functors on the ordinary unbounded
  `DerivedCategory (ProEtaleWeilSheaf k₀ l S)`. Neither an object hypothesis nor a
  bounded/constructible restriction occurs.
- The second conjunct is part (a)'s identity: the native derived direct image along
  `𝟙 S` is naturally isomorphic to `𝟭 (DerivedCategory (ProEtaleWeilSheaf k₀ l S))`.
- The third conjunct is part (b)'s exactness and preservation. Its morphism `j : U ⟶ S`
  has `[IsOpenImmersion j] [QuasiCompact j]`. Exactness is expressed as
  `PreservesFiniteLimits (ProEtaleWeilSheaf.extensionByZero k₀ l j) ∧
  PreservesFiniteColimits (ProEtaleWeilSheaf.extensionByZero k₀ l j)`; the existing
  upstream functor is additive. The termwise descended functor `J_j` is exactly
  `(ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory`.
  For every native derived object `K`, the implication from
  `WeilComplex.objectProperty k₀ l U K` to that same property on `J_j K` expresses
  preservation of bounded constructible cohomology. It does not impose boundedness
  on the domain of `J_j` itself.
- The fourth conjunct is part (b)'s successive-open comparison. Both `j : U ⟶ S` and
  `i : S ⟶ T` are quasi-compact open immersions over the base. The natural isomorphism
  has source `J_j ⋙ J_i` and target `J_(j ≫ i)`, exactly `J_i J_j ≅ J_ij`.
- The final conjunct is the identity-open comparison, with source the termwise
  descended native extension along `𝟙 S` and target the native derived identity functor.
  No redundant open-immersion or quasi-compact identity hypotheses are introduced.
- All four `≅` expressions are isomorphisms in functor categories, hence natural in
  the derived input. Their values lie in the native equivariant categories, so
  Frobenius equivariance is built into every component and its inverse.
  `Nonempty` states the existence asserted by the node, without choosing arbitrary
  comparison data or changing any of the canonical functors.

### Dependency declarations and sources read

The framework dependency's entry module
`WeilConjectures.WeilSheaf.LowerShriek` is publicly imported. Its public chain gives:

- `WeilConjectures.WeilSheaf.Category`: `AlgebraicGeometry.ProEtaleWeilSheaf`,
  `AlgebraicGeometry.WeilSheaf.frobeniusPullback`,
  `AlgebraicGeometry.WeilSheaf.objectProperty`, and
  `AlgebraicGeometry.WeilComplex.objectProperty`.
- `WeilConjectures.WeilSheaf.LowerStar`:
  `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`, the native direct-image functor.
- `WeilConjectures.WeilSheaf.OpenImmersion`:
  `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero`, and its additive,
  finite-limit-preserving and finite-colimit-preserving instances; also
  `AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_extensionByZero`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `CategoryTheory.Functor.rightDerivedFunctor`, computed on K-injectives in the
  ordinary unbounded derived category.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, the descent of the termwise functor.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`, the recorded open-immersion definition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and its import
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`,
  the recorded finite-type dependency's two notions.

The coefficient and constructibility declarations were checked in
`SixFunctors/ProEtale/Adic/Constructible.lean` and the framework's category source.
`IsAdicLisseSheaf` allows a different finite rank on each covering member;
`IsAdicStratifiedLisseSheaf` requires a finite partition by immersed constructible strata;
`IsAdicConstructibleSheaf` imposes that condition locally. `WeilSheaf.objectProperty`
is exactly this property after forgetting the Frobenius pair. The derived property is
`DerivedCategory.TStructure.t.bounded ⊓
DerivedCategory.homologyProperty (WeilSheaf.objectProperty k₀ l S)`.
Thus the theorem uses the required locally finite stratified module predicate,
without identifying the category with fixed pairs in another derived category.

The source places read for part (a) were `WeilSheaf/FiniteLeray.lean`'s
`preservesKInjectiveComplexes_lowerStar` and `rightDerivedLowerStarCompIso`,
`LowerStarComp.lean`'s `lowerStarCompIso`, and `LowerStarId.lean`'s `lowerStarIdIso`.
For part (b), the definition, constructibility theorem, and exactness instances in
`OpenImmersion.lean` were read, together with the cohomology argument in
`LowerShriek.lean`'s `objectProperty_rightDerivedLowerShriek`.
The module imports every currently recorded stated proof-dependency module, privately,
including the corresponding Mathlib matches. Unstated proof dependencies are documented
in the eleven-step proof docstring; no missing proof prerequisite is used as new
statement data.

### Edge cases checked

- Empty schemes are allowed: none of the quantified scheme binders has a nonempty
  hypothesis; the native zero sheaf and empty stratification are allowed by the
  existing predicates.
- The zero complex is allowed, with any vanishing cohomology interval. Part (a)
  also allows arbitrary unbounded native complexes. The constructibility implication
  is confined to part (b).
- The identity is an open immersion and is quasi-compact by existing instances;
  no vacuous identity hypotheses are added.
- A quasi-compact open in a non-quasi-compact locally finite-type scheme is included.
  Quasi-compactness is imposed only on the two named open immersions. Nothing forces
  a globally finite stratification or a global finite-rank bound.
- Arbitrary nonseparated locally finite-type schemes are included, as are
  nonseparated maps in (a). There is no `IsSeparated` binder.
- Successive opens have composite `j ≫ i`, in the correct direction; native functor
  composition is correspondingly `J_j ⋙ J_i`.
- The scheme universe `u` is explicit and arbitrary, matching the recorded native
  framework's universe, with no new site/coefficient universe equalities.

### Searches actually run

- `msearch.py ... leanfinder` query:
  `Natural isomorphisms composition identity of total derived direct image and extension by zero of equivariant Weil sheaves`.
  Result: eight generic module-sheaf pushforward composition/identity hits, including
  `SheafOfModules.pushforward_comp_id`, `pushforward_id_comp`, and `pushforwardNatIso`;
  none states this native derived package.
- `msearch.py ... loogle` query:
  `Functor.rightDerivedFunctorCompIso, Functor.mapDerivedCategoryCompIso`.
  Result: zero hits, unknown identifier `Functor.rightDerivedFunctorCompIso` in
  Mathlib's search service. These general declarations exist upstream instead.
- `msearch.py ... grep` query:
  `rightDerivedLowerStarCompIso|extensionByZero.*(Comp|Id)|mapDerivedCategoryId`.
  Result: zero Mathlib hits.
- `msearch.py ... leansearch` query:
  `composition of derived functors and extension by zero preserves constructible sheaves`.
  Result: eight generic hits, including `mapDerivedCategoryFactorsh` and exact-functor
  Ext/triangulated results; no native Weil comparison package.
- `rg` over both project source roots for
  `extensionByZero.*(Comp|Id)|extensionByZero.*mapDerivedCategory|rightDerivedLowerStarId|nativeWeilBasicComparisons|native_weil_basic_comparisons`:
  the native right-derived composition is already in `FiniteLeray.lean`, but
  identity-direct-image hits elsewhere concern different coefficient categories.
  The extension-by-zero hits concern restriction, internal Hom, or specific
  compactification computations, not the successive/identity derived comparisons.
- `grep -rn lem-sf-native-weil-basic-comparisons lean/WeilConjectures`:
  no existing declaration carrying this blueprint id.
- `rg` in `dag/lean_names_upstream.json` for this node and the chosen declaration
  name: no hit. The upstream composition comparison and exactness instances are
  used as ingredients rather than redeclared notions. No single existing theorem
  or complete collection of native derived declarations states all five conjuncts.

### Validation

`scompile.py NH lem-sf-native-weil-basic-comparisons` compiled the module in module
mode and as its library module successfully, with no errors or non-sorry warnings.
The docstring carries all eleven proof steps and their dependency ids. There are no
new definitions or extra postponed helper theorems. No statement dispute was found.

The worker delivers directly under the current brief. The maintainer's independent
review is the only independent reading; no second worker was started.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
