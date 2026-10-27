## Worker report

Recorded an exact published statement with `existing: true`; no module or new declaration
is delivered. The existing theorem is
`AlgebraicGeometry.ProEtale.isBoundedConstructibleFiniteCoefficient_isTriangulated`
in `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`, lines 126–130. Its full
signature was read locally and confirmed against current server source using
`scompile.py --source Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`.
The node's other fields, including statement and dependency lists, are unchanged.

### Hypotheses and objects

* Any scheme X: `(T : Scheme.{u})`, with no scheme property assumptions.
* Finite commutative ring B: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  `[TopologicalSpace Λ] [DiscreteTopology Λ]` implements its discrete topology.
  No nontriviality, characteristic, quotient-ring or invertibility assumption occurs.
* Small sites: the recorded `Scheme.ProEt`, `Scheme.ProEt.topology` and
  `Scheme.smallEtaleTopology`; their category and covering definitions were read.
  The larger coefficient universe and the standard derived localization implement
  `def-weil-size-convention`; the site object and morphism universes are not equated.
* The ambient unbounded category is exactly
  `ProEtale.FiniteCoefficientDerivedCategory T Λ`. Its module category is
  `FiniteCoefficientModules T Λ`, over `finiteCoefficientRingSheaf T Λ`.
  The latter sheafifies `finiteCoefficientPresheaf`, whose value is
  `C(ConnectedComponents U.unop.left, Λ)` with restriction by precomposition.
  Thus this uses the specified continuous-function coefficient ring sheaf, not a
  substitution of the fixed-scalar or intrinsic-constant-ring category.
* The etale category is `FiniteCoefficientEtaleDerivedCategory T Λ`, the canonical
  fixed-ring presentation of modules over `finiteCoefficientEtaleRingSheaf` by
  `finiteCoefficientEtaleRealization`. The recorded comparison
  `finiteCoefficientComparison` is site inverse image followed by canonical ring-sheaf
  realization; `finiteCoefficientDerivedComparison` is its termwise exact derived functor.
* O_B is precisely `isBoundedConstructibleFiniteCoefficient T Λ`, the existing
  `ObjectProperty.map` of bounded globally constructible etale complexes by that
  derived comparison. Its etale witnesses require, in every cohomological degree,
  a finite `Scheme.Stratification`, constructible strata, and etale-local constant
  finite modules on those strata, together with integers `a ≤ b` and zero cohomology
  outside `[a,b]`. This is the recorded constructibility convention. The full
  subcategory is `FiniteCoefficientBoundedConstructibleDerivedCategory T Λ`.

### Each conclusion

Write P for the recorded O_B predicate, only as explanatory prose here.

* O_B(0): the existing theorem returns `P.IsTriangulated`, which extends
  `P.ContainsZero`. With the essential-image isomorphism closure described below,
  Mathlib `ObjectProperty.prop_zero` gives P of the chosen zero object.
* Isomorphism invariance: unfold only `isBoundedConstructibleFiniteCoefficient`;
  Mathlib's instance `IsClosedUnderIsomorphisms (Q.map F)` applies. The instance's
  body composes the witness isomorphism with the given isomorphism. The iff is
  `ObjectProperty.prop_iff_of_iso`. Automatic instance search does not unfold the
  named predicate by itself; a scratch probe explicitly unfolded it to validate this.
* O_B(N[r]) iff O_B(N) for every integer r: `P.IsTriangulated` extends
  `P.IsStableUnderShift ℤ`. Mathlib
  `ObjectProperty.prop_shift_iff_of_isStableUnderShift`, using the preceding
  isomorphism closure, gives exactly the iff for every integer shift.
* All distinguished triangles and all three implications: the Mathlib
  `ObjectProperty.IsTriangulated` class supplies `IsTriangulatedClosed₂` and its
  rotation instances supply `IsTriangulatedClosed₁` and `IsTriangulatedClosed₃`.
  The corresponding `ext_of_isTriangulatedClosed₁`, `₂`, `₃` have exactly the
  hypothesis `T ∈ distTriang C` and the pairs (2,3), (1,3), (1,2).
  Their iso-closure conclusions become P by the already available essential-image
  isomorphism closure. No assumption of fullness on unbounded objects appears.
* Strictly full triangulated subcategory: `P.FullSubcategory` keeps all ambient
  morphisms; the map-isomorphism-closure instance makes it strictly full, and the
  recorded theorem supplies the triangulated property. Thus the compact existing
  signature and the already defined predicate express every listed clause.

The existing theorem's proof uses bounded-below full faithfulness to lift morphisms
between bounded etale witnesses, then their etale cones; it does not assume that the
unbounded comparison is full. Its source docstring explicitly cites Stacks 09AL and
09B5 and describes these steps. This is an alternative existing implementation of
exactly the node's closure conclusion, so no second theorem is introduced merely to
repackage its fields. The node's accepted proof plan remains unchanged.

### Dependency declarations read and used

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`,
  `Scheme.preservesFiniteLimits_proEtaleSiteComparison`,
  `Scheme.proEtaleSiteComparisonModules`.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the coefficient, module, category,
  comparison and essential-image declarations named above; their definitions and
  docstrings were read, including the exact explicit stratification predicate.
* `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and
  `Etale.BoundedConstructibleDerivedCategory`; the signature and definition match
  bounded finite-module constructible cohomology on the original etale site.
* `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `Pretriangulated`,
  `Pretriangulated.distinguishedTriangles` and rotation axiom;
  `Mathlib.CategoryTheory.Triangulated.Triangulated`: `IsTriangulated`.
* The size-convention node is explicitly metatheoretic and has no declaration.
* The recorded proof declarations were also read:
  `Scheme.finiteRing_constructibleDerived_origin` in
  `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` and
  `Scheme.proEtale_bounded_constructible_isTriangulated` in
  `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`. They use the intrinsic
  constant-ring presentation and are not silently substituted for the required
  continuous-function presentation. No proof-only imports are added because there
  is no newly delivered Lean module.

### Edge cases

The statement allows the zero ring: there is no `[Nontrivial Λ]`. Every scheme,
including the empty scheme and schemes that are not Noetherian or quasi-compact,
is allowed without any extra instance. The existing predicate permits empty finite
stratifications on the empty scheme, and arbitrary integer cohomological bounds;
zero cohomology can use any nonempty finite interval. The shift is indexed by all
of ℤ, so zero and negative shifts are included. All three triangle positions are
covered. The unbounded ambient category places no boundedness hypothesis on an
arbitrary object before O_B is tested. Finite rings can always be represented in
`Type (u + 1)`; no new universe equality or site-size restriction is imposed.

### Searches

* `msearch.py ... leanfinder` query: "bounded constructible etale origin is
  triangulated in the pro etale derived category". Eight results, including
  `DerivedCategory.instIsTriangulated`, derived exact-functor triangulatedness and
  the homological-kernel triangulated instance; none states this geometric predicate.
* `msearch.py ... loogle` query: `"ObjectProperty", "IsTriangulated", "map"`.
  Three results, including
  `CategoryTheory.ObjectProperty.instIsTriangulatedMapOfIsTriangulatedOfFull`.
  This abstract result alone would require fullness and is not the desired theorem.
* `msearch.py ... grep` query:
  `constructible.*(triang|[Oo]rigin)|pro[Ee]tale.*constructible`. Zero Mathlib hits.
* `rg` of `lean/WeilConjectures` for constructible/triangulated and origin/triangulated
  names found general fixed-coefficient and bounded-below origin results, not this
  coefficient-ring presentation. Search for the item's full node id found no match.
* `rg` of `lean/Sheaf` for `isBoundedConstructibleFiniteCoefficient` and
  `finiteCoefficientDerivedComparison` found the exact theorem in
  `PullbackBoundedConstructible.lean:126`, plus uses in restriction/direct-image
  material. Full source and docstring were read, then confirmed from the server.
* `rg` of `dag/nodes` found the same theorem already listed as an auxiliary
  declaration of `lem-weil-pbc-pullback-preserves-bounded-constructible`. Reusing
  this published declaration is required by the one-definition-per-notion rule.
* Read Mathlib `Triangulated/Subcategory.lean`, `ObjectProperty/Shift.lean`,
  `ObjectProperty/ContainsZero.lean`, and `ObjectProperty/ClosedUnderIsomorphisms.lean`
  to verify precisely how every explicit conclusion is encoded by the existing
  theorem and the essential-image predicate.

Source verification: read `literature/stacks-project/proetale.tex`,
`lemma-compare-constructible-derived` (09AL) and `lemma-constructible-serre` (09B5).
These describe strictly full triangulated constructible-cohomology subcategories
and bounded-below comparison. The recorded Lean predicate retains the blueprint's
stronger global finite-stratification convention, as this node requires.

### Validation

A sandbox-only, module-mode probe compiled through `scompile.py` checks the existing
closure theorem, synthesizes its triangulated instance, explicitly unfolds the
essential-image predicate for its isomorphism-closure instance, and checks the zero,
isomorphism, shift-iff and three distinguished-triangle implication APIs. No scratch
file is delivered. The first probe exposed only that the named predicate is not
unfolded automatically during instance synthesis; adding explicit unfolding in the
probe resolves this without any library change or additional hypothesis.

No new nodes, dependency repairs, statement correction or statement dispute.
The delivery wrapper additionally checks the recorded existing declaration on the server.

## Second reading by Q128

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
