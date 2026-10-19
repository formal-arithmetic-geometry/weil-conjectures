## Worker report

Existing declaration: `AlgebraicGeometry.Etale.derivedBaseChangeMap`, in
`WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`, lines 123–126 of
slopmaster2. No delivered Lean module, new node, dependency module, or statement
correction. Only the item's `lean` field changes.

Read the source blueprint definition at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-unbounded-exchange.md`,
the complete expanded node, all thirteen statement dependencies and their records,
and the recorded Lean declarations and docstrings. The source's unbounded map
already implements exactly the specified construction. Its generic coefficient
category is specialized to `ModuleCat.{u + 1} Λ`; its component at `K` is the
node's exchange morphism. Repeating this as a new definition would violate the
one-definition rule.

Clause-by-clause correspondence:

- Schemes and four edges: the existing declaration has implicit
  `{X' X Y' Y : Scheme.{u}}`, `{g' : X' ⟶ X}`, `{f' : X' ⟶ Y'}`,
  `{f : X ⟶ Y}`, `{g : Y' ⟶ Y}`. A cartesian square is supplied as
  `sq : IsPullback g' f' f g`; use `sq.toCommSq` with equality
  `g' ≫ f = f' ≫ g`. The chosen pullback identification affects this
  construction only through this equality and its induced inverse-image
  comparison, as in the recorded `squareUpperStarIso`.
- Arbitrary commutative ring: specialize the explicit parameter `A` to
  `ModuleCat.{u + 1} Λ`, with `Λ : Type (u + 1)` and `[CommRing Λ]`.
  All abelian, Grothendieck, symmetric closed monoidal and functorial flat
  resolution instances are supplied by the library. None is an extra ring
  hypothesis. In particular no finiteness, torsion or invertibility is required.
- The module derived categories are exactly `DerivedCategoryModule Λ T`,
  definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat Λ))`,
  the encoding recorded by `def-weil-pbc-derived-categories`.
- Exact constant-coefficient inverse images and their sheaf adjunction are
  `Etale.upperStar (ModuleCat Λ) u` and
  `Etale.upperStarLowerStarAdjunction (ModuleCat Λ) u`. The module-sheaf
  encoding is the existing six-functor encoding prescribed by the dependency
  record, not a new copy of sheaves over the constant ring.
- The notation `L((u)^*[A])` is the total derived pullback. Since `upperStar`
  is exact, `leftDerivedUpperStarIsoMapDerivedCategory A u` canonically
  identifies it with `D((u)^*[A])`, the termwise induced functor.
  `Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac` specifies
  compatibility with localization. This canonical identification is explicit
  in upstream, rather than an assumption identifying arbitrary derived functors.
- `R((u)_*[A])` is `Functor.rightDerivedFunctor` of direct image. Its
  derivability structure uses K-injectives; hence a K-injective resolution
  computes it as `Q(u_* I)`. The existing source's `DerivedLowerStar` section
  explicitly identifies it as total unbounded derived direct image.
- The canonical adjunction and its unit/counit are
  `Etale.derivedUpperStarLowerStarAdjunction A u`, defined from the sheaf
  adjunction via `.derivedAdjunction`. No arbitrary adjunction is supplied.
- The square comparison is `Etale.derivedSquareUpperStarIso A sq.toCommSq`:
  `(leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).symm ≪≫
  leftDerivedUpperStarComp A g' f`.
  In `UpperLowerStar.lean`, `leftDerivedUpperStarComp` applies
  `Functor.leftDerivedFunctorNatIso` to the sheaf `upperStarComp` and then
  `Functor.leftDerivedFunctorCompIso`. Both of these are defined in
  `LeftDerivedFunctor/MapDerivedCategory.lean` by transporting the termwise
  comparison along the canonical exact-functor identifications above.
  Thus it is precisely the descended termwise comparison, in the canonical
  derived-pullback coordinates. Localization uniqueness gives the node's
  specified comparison; no unrelated square isomorphism is chosen.
- The morphism's source and target are the components of the signature
  `R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A])`.
  For `K : DerivedCategoryModule Λ X`, take
  `(Etale.derivedBaseChangeMap (ModuleCat Λ) sq.toCommSq).app K`.
  Lean's `⋙` order gives exactly `g⁻¹ Rf_* K ⟶ Rf'_* g'⁻¹ K`.
- Its data are literally `(derivedBaseChangeSquare A sq).natTrans`, where
  `derivedBaseChangeSquare` is `mateEquiv` for the derived adjunctions at
  `f` and `f'` applied to the square comparison's `.hom`.
  `derivedUpperStar_map_derivedBaseChangeMap_app_counit` in the same module
  records the exact transpose: the square comparison at `Rf_* K` followed
  by `Lg'^*` of the counit at `K`.
- Unfolding Mathlib `mateEquiv` gives the equivalent displayed formula:
  the unit at `Lg^* Rf_* K`, then `Rf'_*` of the square comparison, then
  `Rf'_* Lg'^*` of the counit. Functor reassociations only insert identities
  at components. No isomorphism assertion about the resulting map occurs.
- For integer coefficients this same construction specializes to abelian
  sheaves, under the usual equivalence of integer modules with abelian
  groups. The dependency's bounded square is the restriction of the same
  termwise comparison. The node asks for the same mate formula as the
  bounded exchange, not a new theorem proving bounded/unbounded coherence.

Dependency declarations read and matched (module, declaration):

1. `WeilConjectures.SixFunctors.BaseChange.Square`,
   `AlgebraicGeometry.Etale.squareUpperStarIso`.
2. `Sheaf.AlgebraicGeometry.DerivedCategories`,
   `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`, with its
   documented existing `DerivedCategoryModule` and `DerivedCategory.homologyFunctor`.
3. `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
   `AlgebraicGeometry.etaleInverseImageModulesExact` (the constant-ring
   transport and exact module adjunction; no duplicate is required).
4. `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
   `CategoryTheory.Functor.mapDerivedCategoryPlus`, together with the
   unbounded `mapDerivedCategory` of which it is the restriction.
5. `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
   `CategoryTheory.Functor.exactFunctor_derivedFunctor`.
6. `Sheaf.AlgebraicGeometry.KInjectiveResolutions`,
   `CochainComplex.IsKInjectiveResolution` (Mathlib K-injectivity and `QuasiIso`).
7. `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`,
   `CochainComplex.etale_kinjective_resolutions_exist`.
8. `Sheaf.CategoryTheory.KInjectiveTotalDerived`,
   `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
9. `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`,
   `CategoryTheory.Adjunction.exists_derived_adjunction_of_essentially_constant`.
10. `Mathlib.CategoryTheory.Localization.Predicate`,
    `CategoryTheory.Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso`,
    `natTrans_ext`, as specified by this dependency's `mathlib_match`.
11. `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`,
    `AlgebraicGeometry.Etale.pullbackSquareComparison` (bounded comparison).
12. `Mathlib.CategoryTheory.Adjunction.Mates`, `CategoryTheory.mateEquiv`.
13. `WeilConjectures.SixFunctors.BaseChange.Derived`,
    `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`; also read the mate
    implementation `Etale.baseChange` in `MorphismDefs`.

These are mathematical ingredients already implemented by the existing source
construction; this existing attachment creates no module whose imports could
replace or duplicate those dependencies. Generic existence theorems do not need
to be reproved or repackaged merely to attach an existing definition.

Edge cases checked: arbitrary unbounded `K` (no boundedness or cohomological
finiteness); empty schemes; zero complex; zero coefficient ring; `Λ = ℤ`;
identity squares and arbitrary cartesian squares. The construction imposes no
properness or other geometric condition and claims no invertibility. The
coefficient and sheaf universes match the project's derived-category encoding.
The upstream generic definition also accepts noncartesian commutative squares;
specializing it to the node's cartesian squares changes neither formula nor data.
No statement dispute or node correction.

Searches performed:

- `msearch.py ... leanfinder "unbounded derived exchange morphism mate of the inverse image square comparison and counit"`:
  eight generic derived-adjunction/localization hits, no scheme exchange.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, AlgebraicGeometry.Etale.derivedBaseChangeMap"`:
  zero hits; the upstream-specific name is unknown to Mathlib's index.
- `msearch.py ... grep "derivedBaseChangeMap|unbounded.*exchange" CategoryTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "unbounded derived base change morphism etale sheaves modules"`:
  service unavailable (Internal Server Error); no conclusion drawn from this.
- `rg` over `WeilConjectures` for `derivedBaseChangeMap`, `unboundedExchange`
  and `unbounded.*exchange`: found the exact definition in
  `SixFunctors/BaseChange/DerivedUnbounded.lean:123`, alongside the distinct
  bounded and pro-etale constructions. Searching for the literal node id
  gave no upstream attachment. This is the small etale construction.
- `rg` over `lean/Sheaf` for the same patterns: bounded exchange citers,
  no additional definition of the unbounded exchange.
- `rg` of `dag/lean_names_upstream.json`: no exact entry for the unbounded
  declaration (the older name table includes bounded exchange); direct
  source inspection found and verified it.

Validation: a scratch probe `scratchpad/ExistingProbe.lean` imported the existing
unbounded map and coefficients, printed its full type, and instantiated its
component for arbitrary `Λ`, cartesian square, and `K` with no auxiliary instance
assumptions. `scompile.py NE def-kun-unbounded-exchange .../ExistingProbe.lean`
passed cleanly on the server in 2.6 seconds, nice 19, two threads, 60-second
limit. No local Lean or Lake invocation. This scratch probe is not delivered.

## Second reading by NE

I independently read the node statement and the recorded declaration. The node introduces a cartesian square of schemes with edges `f : X ⟶ Y`, `f' : X' ⟶ Y'`, `g : Y' ⟶ Y`, and `g' : X' ⟶ X`, a commutative ring `Λ`, the module derived categories `D(T_ét, Λ)`, exact inverse images left adjoint to direct images, their unbounded derived functors and K-injective resolutions, the canonical derived adjunctions with units and counits, and the descended square isomorphism. The conclusion defines, for `K`, a morphism `g⁻¹ Rf_* K ⟶ Rf'_* g'⁻¹ K` as the mate of the square comparison followed by the counit, equivalently the displayed unit–comparison–counit composite, with no isomorphism claim.

The existing declaration `AlgebraicGeometry.Etale.derivedBaseChangeMap` in `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded` renders the conclusion as `def derivedBaseChangeMap (sq : CommSq g' f' f g) : R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A])`. Specializing `A` to `ModuleCat.{u + 1} Λ` and `sq` to `sq.toCommSq`, its component at `K` has exactly the node's source and target. Its implementation is `mateEquiv` of `derivedSquareUpperStarIso` under `derivedUpperStarLowerStarAdjunction`, so it is exactly the stated mate and carries the same unit–comparison–counit formula. The declaration is generic over commutative squares; restricting to cartesian squares adds no hypothesis to the construction. Its derived categories, exact termwise inverse images, K-injective right derived direct images, and canonical adjunctions are the recorded dependency notions. No extra finiteness, properness, boundedness, characteristic, or invertibility assumption occurs.

Edge cases remain covered: empty schemes and identity/cartesian squares, zero complexes, `Λ = ℤ`, and the zero commutative ring; `K` is arbitrary and unbounded. Universes specialize compatibly to the module encoding. I found no mismatch and changed only the recorded signature string to the exact source signature (removing `noncomputable` from the record); no Lean module or definition was added. Searches and dependency checks in the worker report were verified against the source declaration and its docstring; they found no competing definition.
