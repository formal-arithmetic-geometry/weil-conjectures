## Worker report

The module `Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection` states
`CategoryTheory.Functor.exactAdjointForgetDerivedDetection`, with one `sorry` and no
new definitions. The node is unchanged outside `lean`. No statement correction,
new node, dependency repair, or disputed mathematical assertion is needed.

Hypotheses and clauses, checked against the node and its four proof steps:

- The abelian categories are `A : Type uA`, `B : Type uB`, with explicitly bound
  `Category.{vA}`, `Category.{vB}`, `Abelian`, and independently chosen
  `HasDerivedCategory.{wA}`, `HasDerivedCategory.{wB}` instances. These are the
  ordinary unbounded localizations. No universe equality, smallness, resolutions,
  or enough-injectives assumption is imposed.
- The node's left adjoint A is named `F : A ⥤ B` to distinguish it from the category.
  The forgetting functor is `U : B ⥤ A`. Both have `Additive`,
  `PreservesFiniteLimits`, and `PreservesFiniteColimits` instances: exactly the two
  additive exact functors in the statement. `_adj : F ⊣ U` is the given adjunction;
  `[U.ReflectsIsomorphisms]` is conservativity.
- `U.PreservesInjectiveObjects` uses Mathlib's extension-along-monomorphisms
  definition `CategoryTheory.Injective`. `U.PreservesKInjectiveComplexes` uses the
  upstream preservation class and Mathlib's `CochainComplex.IsKInjective`, whose
  field says every map from an acyclic complex is homotopic to zero.
- `U.mapDerivedCategory` is the existing termwise induced functor. The conclusion
  `IsTriangulated` uses its existing `CommShift ℤ` structure, so includes the shift
  and distinguished-triangle compatibilities. `ReflectsIsomorphisms` is derived
  conservativity.
- For every `r : ℤ`, `chi` is a natural isomorphism
  `U.mapDerivedCategory ⋙ H_A^r ≅ H_B^r ⋙ U`. The equation identifying it with
  `(U.mapDerivedCategoryHomologyFunctorIso r).symm` specifies the canonical
  comparison, rather than allowing an arbitrary isomorphism. Its inverse at `Q K`
  is explicitly the existing normalized kernel/image/quotient comparison's inverse,
  transported through `homologyFunctorFactors` and `mapDerivedCategoryFactors`.
  The displayed equation is the signature of the upstream
  `mapDerivedCategoryHomologyFunctorIso_hom_app_Q` with F = U. Thus the orientation
  of chi is H D(U) to U H, whereas its inverse has the node's theta orientation.
- Being a natural isomorphism on the entire derived category makes chi compatible
  with every derived morphism, in particular every localized chain map and inverse
  quasi-isomorphism. The representative formula fixes its descent normalization.
  The extra homotopy clause explicitly says `Homotopy f g` induces
  `Nonempty (Homotopy (U_* f) (U_* g))`, for every pair of unbounded complexes and
  chain maps. Together these give the specified chain-map, homotopy, and localization
  compatibilities without imposing choices of representatives.
- The implication for each `f : K ⟶ L` returns all three conclusions in order:
  `∀ r, IsIso (U.map (H_B^r.map f))`, `∀ r, IsIso (H_B^r.map f)`, and `IsIso f`,
  under the explicit premise `IsIso (U.mapDerivedCategory.map f)`.
- Finally, for every integer r, `sigma` is the natural single-degree comparison,
  explicitly equal to `U.mapDerivedCategorySingleFunctor r`. Evaluating at M gives
  the single-degree object comparison. Mathlib's `singleFunctor B r` puts M in
  cohomological degree r; with the usual shifted-degree-zero interpretation of
  M[r], evaluate the quantified comparison at -r. All integer degrees are covered,
  so neither convention excludes or changes a case. The equality to the existing
  construction specifies the canonical comparison.

Dependency declarations and signatures read:

- `def-sp-abelian`: `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`
  (normal monos/epis, preadditive, finite products, kernels and cokernels).
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `Qh`, and `quotientCompQhIso`;
  `HomologySequence` supplies `homologyFunctor` and its factorization.
- `def-sfb-right-derived-functor`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and the other
  five recorded declarations were read. Its public imports supply the existing
  K-injective interface; the present exact-functor statement does not assume the
  resolution hypothesis required to construct that right-derived pair.
- `def-sp-injective-resolutions`:
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `CategoryTheory.Injective`;
  used through the public `Injective.Preserves` module and preservation class.
  The resolution notion is not needed, only injectivity.
- Proof imports: `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`,
  `CategoryTheory.Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`,
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes` (public because its
  preservation class occurs in the statement);
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategorySingleFunctor`;
  `Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence`,
  `CategoryTheory.Functor.exactDerivedCohomologyCoherence`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.isIso_iff`. The normalized comparison is publicly supplied by
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Sources checked: Stacks `homology.tex`, `lemma-adjoint-preserve-injectives` (015Z),
`derived.tex`, `lemma-adjoint-preserve-K-injectives` (08BJ) and
`lemma-right-derived-exact-functor` (015F); the source's generalized detection argument
in `IsoAlgebraComp.lean`, `isIso_of_isIso_forget_mapDerivedCategory_map`. The K-injective
argument requires exactness of the left adjoint, not boundedness or injective resolutions.
The detection argument uses exactly cohomology naturality and conservativity.

Edge cases checked: the identity adjunction, the zero abelian category, zero complexes,
zero objects, degree zero, and both positive and negative single degrees satisfy all
clauses. A zero functor out of a nonzero category is excluded by conservativity, as it
must be. Unbounded complexes are quantified directly throughout. Independent category,
hom, and localization universes remain independent. The adjunction is oriented F ⊣ U,
so maps into U(I) correspond to maps from F(M) into I, as required by 08BJ.

Searches actually run using the prescribed msearch wrapper:

- LeanFinder: “An exact conservative right adjoint with exact left adjoint preserves
  injectives and K-injective complexes and induces a conservative triangulated functor
  on unbounded derived categories”. Eight hits, including mapDerivedCategory,
  mapDerivedCategoryFactors(h), and its triangulated instance; no combined statement.
- Loogle: `CategoryTheory.Functor.mapDerivedCategory,
  CategoryTheory.Adjunction.preservesKInjectiveComplexes`: zero hits, the second name
  is not in the Mathlib service. A second query for the first name alone found its
  construction and related declarations (see sandbox search log).
- Mathlib grep: `mapDerivedCategoryHomologyFunctorIso|ReflectsIsomorphisms.*mapDerivedCategory`
  in `Algebra/Homology/DerivedCategory`: no hits; the normalized comparison lives upstream.
- Local rg in `lean/WeilConjectures/CategoryTheory/DerivedCategory` and
  `lean/Sheaf/CategoryTheory` for `ReflectsIsomorphisms`,
  `mapDerivedCategoryHomologyFunctorIso`, `preservesKInjectiveComplexes`, and the proposed
  name found the recorded ingredients and specialized applications, not this combined
  general statement. Searching the item id in `lean/WeilConjectures` found none.
  Read the full signatures/docstrings of all recorded dependencies above before writing.

Validation: compile through scompile.py. The initial compile exposed a module visibility
issue for `PreservesInjectiveObjects`; making `Mathlib...Injective.Preserves` public
repairs that interface without changing the mathematical statement. Final compile and
maintainer preflight results are recorded by deliver2.py.

## Second reading by Q87

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
