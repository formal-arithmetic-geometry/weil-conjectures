## Worker report

The module `lean/Sheaf/CategoryTheory/SimplexNerveCommaPullback.lean` states
`SSet.Enhanced.simplex_nerve_comma_pullback` and defines the helper
`SSet.Enhanced.simplexUndercategoryTarget`.  Mathlib's `X.Elementsᵒᵖ` is used for
`C = S(X)`: an arrow from the simplex `rho` to `tau` is the opposite of the
category-of-elements arrow and therefore has the required monotone map
`[n] -> [m]` with `tau Delta(alpha) = rho`.  An arbitrary full subcategory is
represented by `P : ObjectProperty (X.Elementsᵒᵖ)` and `P.FullSubcategory`; its
inclusion is `P.ι`.  The ordinary undercategory is
`StructuredArrow sigma (𝟭 X.Elementsᵒᵖ)`, and its full subcategory on targets in
`P` is
`(P.inverseImage (StructuredArrow.proj sigma (𝟭 X.Elementsᵒᵖ))).FullSubcategory`.
The helper `simplexUndercategoryTarget` is the canonical functor from that full
subcategory to `P.FullSubcategory`, sending an under-arrow to its target.

The theorem renders the statement clause by clause as follows.

* The first conjunct is `Quasicategory (CategoryTheory.nerve X.Elementsᵒᵖ)`.
  The second is quasicategoricity of the ordinary undercategory nerve
  `Quasicategory (CategoryTheory.nerve (StructuredArrow sigma (𝟭 X.Elementsᵒᵖ)))`.
  No quasicategory instance or other hypothesis on `X` is assumed.
* The displayed existential `e₀` is the canonical nerve/coherent-undercategory
  isomorphism.  Its equation says that it is over `N(C)`: after the isomorphism,
  the coherent projection
  `commaSubcomplex ... false).ι ≫ fst ...` is exactly
  `CategoryTheory.nerveMap (StructuredArrow.proj sigma (𝟭 X.Elementsᵒᵖ))`.
  The `false` endpoint convention in `comma` is the outgoing arrow
  `sigma -> c` convention.
* `IsIsofibration (...)` states the required inner-fibration and equivalence-edge
  lifting property for that coherent projection.
* The `e₁` existential gives the strict pullback isomorphism from the nerve of the
  full ordinary comma `(sigma downarrow B)` to
  `pullback (CategoryTheory.nerveMap P.ι) q`.  Its first equation identifies the
  pullback's `P` projection with the nerve of `simplexUndercategoryTarget`; its
  second equation identifies the coherent projection with the composite of the
  full-subcategory inclusion and `e₀`.  Thus the isomorphism is the specified
  square isomorphism, not an unrelated equivalence.
* The final universal conjunct is, for every small quasicategory `Q`,
  `IsWeakHomotopyEquivalence (pullbackCoreComparison q (nerveMap P.ι) Q)`,
  which is the canonical comparison of the strict pullback with the homotopy
  pullback in `Cat_infty`.

The four dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.comma`, `SSet.Enhanced.commaSubcomplex`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and `SSet.Enhanced.Quasicategory`;
* `Sheaf.CategoryTheory.IsofibrationExponentiation`,
  `SSet.Enhanced.IsIsofibration`;
* `Sheaf.CategoryTheory.IsofibrationPullbackLimit`,
  `SSet.Enhanced.pullbackCoreComparison`;
* Mathlib `CategoryTheory.nerve`, `CategoryTheory.nerveMap`,
  `CategoryTheory.Functor.Elements`, `ObjectProperty.FullSubcategory`, and
  `StructuredArrow`.

Edge cases checked before writing: `X` may be empty; `P` may be empty or all of
`C`; `sigma` is any chosen simplex, including a degenerate simplex and a
0-simplex; and no nonempty or quasicategory assumption is added.  For `P = empty`
the strict pullback and the full comma nerve are empty.  For `P = top` the strict
pullback is the coherent undercategory itself.  The identity under-arrow gives a
vertex of the ordinary undercategory for every supplied `sigma`.  The construction
uses all simplices, including degenerate ones, as required by the category of
simplices.

Searches made:

* `msearch.py ... leanfinder "nerve of the simplex category of a simplicial set and coherent undercategory pullback"` returned Mathlib nerve declarations (`CategoryTheory.nerve`, `nerveFunctor`, `Nerve.isStrictSegal`) but no comma-pullback theorem.
* `msearch.py ... loogle "CategoryTheory.nerve, CategoryTheory.StructuredArrow, SSet.Enhanced.comma"` returned zero hits (the service reported unknown `SSet.Enhanced.comma`).
* `msearch.py ... grep "Elements|StructuredArrow|commaSubcomplex" AlgebraicTopology` found only ordinary Mathlib category-of-elements/structured-arrow and unrelated simplicial hits; no theorem matching this statement.
* `rg` over `WeilConjectures/` and the project's `lean/Sheaf/` found no declaration of this node; the only related project text is the proof plan in `SimplexFirstVertexCoconeEquivalence`.
* The dependency node files and their recorded declarations were read in full.  The recorded interfaces used are the existing coherent `comma`, `IsIsofibration`, and `pullbackCoreComparison` declarations listed above.

No statement correction, `STATEMENT-DISPUTED` flag, new definition node, or
dependency module was needed.  The helper is part of the item's canonical
undercategory construction and is recorded in the item's `lean.declarations`.

## Second reading by Q26

I reread the node and its source clause by clause.  The binders `X`, `P`, and
`sigma` supply exactly the small simplicial set, arbitrary full subcategory, and
chosen simplex.  `X.Elementsᵒᵖ` has precisely the monotone-map orientation in the
node; `StructuredArrow` supplies objects `sigma -> c` and commuting morphisms;
`comma ... false` supplies the coherent outgoing arrows.  The first isomorphism
and its projection equation state the nerve/coherent identification over `N(C)`.
The isofibration clause is stated for that same projection.  The second isomorphism
uses the same `e₀`, the full-subcategory target functor, and both pullback
projections, so it states the strict full-subcategory pullback.  The final clause
uses the exact published homotopy-pullback comparison for every test `Q`.
No hypothesis on `X` was added, no clause was dropped, and universes are explicit.
The file was compiled with `scompile.py`; it produced no errors or warnings.
