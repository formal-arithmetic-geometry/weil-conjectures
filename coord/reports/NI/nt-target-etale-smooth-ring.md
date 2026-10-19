## Worker report

The module `Sheaf.Targets.EtaleSmoothRing` states
`AlgebraicGeometry.Etale.isIso_baseChange_of_smooth_of_ring_order_invertible`.
Its sole proof is `sorry`; no construction or definition is added. The statement is the
signature of the specified upstream-master source theorem, with its surrounding variables
moved into explicit binders. The full five-step DAG proof plan is in its docstring.

Clause-by-clause reading:

- “Λ a commutative ring”: `(Λ : Type (u + 1)) [CommRing Λ]`. This is precisely the
  coefficient size used in the source and the existing six-functor encoding.
- Schemes X, Y, X′, Y′: `{X Y X' Y' : Scheme.{u}}`, with arbitrary `universe u`.
- f:X→Y: `{f : X ⟶ Y}`; “quasi-compact and quasi-separated”:
  `[QuasiCompact f] [QuasiSeparated f]`.
- g:Y′→Y smooth: `{g : Y' ⟶ Y} [Smooth g]`.
- The upper and left maps: `{g' : X' ⟶ X}` and `{f' : X' ⟶ Y'}`.
- Cartesian square: `(sq : IsPullback g' f' f g)`. As in the source, this includes
  the commutative-square data; `sq.toCommSq` supplies the exchange construction.
  `IsPullback` is the universal-property presentation of the chosen fibre-product
  identification recorded in `ChosenCartesianSquare`, with the same projection equations.
  There is no extra assumption that X′ is literally Mathlib's selected pullback.
- “for every a∈Λ its additive order, viewed in Γ(Y,top), is a unit”:
  `(htor : ∀ a : Λ, IsUnit (addOrderOf a : Γ(Y, ⊤)))`. The natural-number cast is into
  the global regular-function ring of Y, not into Λ.
- The conclusion is `IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)`.
  It concerns the actual natural transformation, not merely an isomorphism of its
  endpoints or an assertion for a specially chosen complex. Its domain is the bounded
  below derived category of module-valued small-etale sheaves on X and its target is
  that on Y′, by the read signature of `Etale.baseChange`.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, defined by quasi-compactness of the diagonal.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, extending `CommSq` with `isoPullback`,
  `hom_fst` and `hom_snd`. Imported rather than copied. The target uses the source's
  equivalent `IsPullback` binder as described above.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the dependency's mixed record uses
  `CategoryTheory.Sheaf` on `smallEtaleTopology` and `ModuleCat.{u+1} Λ` for six-functor
  coefficients. Its set-valued local-constancy predicates are irrelevant here. The module
  was absent locally; its full current source was read with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, and its public imported upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, and the
  underlying `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} Λ)` category.
- `WeilConjectures.SixFunctors.BaseChange.Derived`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, and the same dependency's recorded
  `AlgebraicGeometry.Etale.baseChange` in
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
  The latter is exactly the target's source map: unit insertion, canonical square
  comparison, counit contraction. Both recorded modules are imported.

The available proof-dependency modules are imported without `public`, including constant-ring
module equivalence, coefficient forgetting, allowable torsion, geometric stalks, derived
inverse image, and the unbounded base-change map. The proof-dependency nodes
`sbc-thm-bounded-below-derived-smooth-base-change` and `sbc-thm-smooth-base-change` have no
recorded Lean declaration, so there is no module to import for them yet. They are not needed
to type this statement; their lack of a proof import is not a statement-dependency wait.

Edge cases checked before writing:

- The empty base scheme is allowed. Its zero global-section ring makes zero a unit,
  so the hypothesis need not force positive characteristic in this case.
- `addOrderOf` is zero for elements of infinite additive order. No positivity or
  nonzero-order assumption is inserted. At a nonempty base, the hypothesis at 1 rules
  out infinite order; the docstring handles the empty case by absence of geometric points.
- The zero coefficient ring is permitted; `addOrderOf (1 : Λ)` is then 1, and the module
  category has only zero objects up to isomorphism. There is no `Nontrivial Λ` binder.
- No nonemptiness, connectedness, characteristic, separatedness of schemes, constructibility,
  bounded-above condition, or smoothness of f is added.
- Arbitrary pullback squares, including identity maps, are retained.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "Smooth base change natural transformation derived etale
  sheaves modules ring additive order invertible"`: eight hits, concerning Kähler
  differentials, formal etaleness, and algebraic base change; none is the desired theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, CategoryTheory.IsIso"`: one hit,
  `Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth`, about normalization, not etale
  derived sheaves.
- `msearch.py ... grep "baseChange.*smooth|smooth.*baseChange" AlgebraicGeometry`:
  five hits about stability of smoothness under base change, no exact theorem.
- `rg -n 'isIso_baseChange_of_smooth|smooth.*baseChange|baseChange.*smooth'` in
  `WeilConjectures/` and `lean/Sheaf`: the existing upstream
  `Etale.isIso_baseChange_app_of_smooth` requires allowable-torsion cohomology of a fixed
  complex; its full signature and neighboring lemmas were read. It does not state the
  ring-order hypothesis or a functor isomorphism, so is not an exact reuse.
- Search for the item id in upstream `WeilConjectures/`: no hits. The target name occurs
  in the designated literature snapshot, whose complete `Smooth.lean` was read, but not
  in the published source checkout. `scompile.py --source` confirms that the module
  `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Smooth` is unavailable on the server.
  Thus the new declaration does not duplicate an available upstream declaration.

No node faults or disputed statements were found. No new nodes or dependency repairs.

## Second reading by NI

I independently opened the node, the delivered Lean module, and the complete designated
source `literature/upstream-master-20261014/WeilConjectures/SixFunctors/Etale/
BaseChangeTheorems/Smooth.lean`. This target's source is that Lean snapshot, rather than
an individual Stacks lemma. Its surrounding variables require exactly the coefficient
universe, four schemes and maps, and qcqs hypotheses shown below. I also read Stacks
0EYU (smooth base change), 07A7 (the adjunction mate), and 0D6J (module/abelian comparison)
in the local TeX sources for the mathematical background of the proof plan.

Object/hypothesis/conclusion checklist (every entry passes):

- A commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`, exactly the
  source's variables. No field, nontriviality, finite ring, or characteristic instance.
- Four arbitrary schemes: `{X Y X' Y' : Scheme.{u}}`; the single declared universe `u`
  is arbitrary, with coefficient size `u+1` as in the designated target source and the
  recorded six-functor convention. There is no independently smaller test universe.
- The original map and its qcqs assumptions: `{f : X ⟶ Y}`,
  `[QuasiCompact f] [QuasiSeparated f]`. No properness or Noetherian assumption.
- The smooth base-change map: `{g : Y' ⟶ Y} [Smooth g]`. Smoothness is on g, not f.
- The two remaining arrows: `{f' : X' ⟶ Y'} {g' : X' ⟶ X}`, with the correct endpoints.
- Cartesian square: `(sq : IsPullback g' f' f g)`. I read `ChosenCartesianSquare`
  and Mathlib `IsPullback`, `IsPullback.isoPullback`, and its two projection equations.
  The latter supplies the former's specified identification, uniquely determined by
  the projections. Conversely that identification gives the universal property.
  Thus using the source's `IsPullback` neither restricts nor generalizes the geometry;
  `sq.toCommSq` retains precisely the square equality used by the exchange map.
- Every additive order is invertible on Y: `(htor : ∀ a : Λ,
  IsUnit (addOrderOf a : Γ(Y, ⊤)))`. The cast is into the global function ring of Y.
  The universal quantifier has not been replaced by a condition just at 1.
- Conclusion: `IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq)`.
  I read the full `MorphismDefs` construction: it is the unit insertion, derived
  composition comparison and counit contraction, from `Rf_* ⋙ Lg^*` to
  `Lg'^* ⋙ Rf'_*` on D-plus. This is the actual transformation as an isomorphism
  of functors, not just an unspecified endpoint isomorphism or a selected component.

Dependency interfaces were independently read: Mathlib `Scheme`, `QuasiSeparated`
(quasi-compact diagonal), `Smooth` (affine-local smooth ring maps), the project's
`ChosenCartesianSquare` and `DerivedCategories`, upstream `Derived.Coefficients`
(`DerivedCategoryModule` is D of module-valued small-etale sheaves), and both recorded
exchange declarations (`derivedBaseChangeMapPlus` and `baseChange`). The current server
`WeilConjectures.AlgebraicGeometry.EtaleSheaves` was read with `scompile.py --source`;
its mixed record does not force set-valued coefficients here. No dependency module or
new node is supplied by this delivery. No statement correction or citer audit is needed.

Edge cases pass: empty schemes and identity squares remain admissible; no index or
nonemptiness hypothesis appears. The zero coefficient ring remains allowed. Infinite
additive order is represented by zero and is not silently excluded; on an empty Y,
zero is a unit in its zero global ring. On a nonempty base the given hypothesis rules
that case out mathematically. No extra positive integer or characteristic assumption
is introduced. No bounded-above or constructibility condition appears; bounded below
is precisely the domain of the source transformation. All variables and universes are
explicitly bound.

Independent duplicate searches:

- LeanFinder via `msearch.py`: “Invertible exchange morphism for etale cohomology with
  torsion ring coefficients under smooth pullback”: eight hits in algebraic etaleness
  and Kahler differentials, no exact theorem.
- Loogle via `msearch.py`: `addOrderOf, IsUnit`: zero hits.
- `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for
  `ring_order_invertible` and `isIso_baseChange_of_smooth_of_ring_order_invertible`:
  no available duplicate. Broader smooth/base-change searches found upstream
  `Etale.isIso_baseChange_app_of_smooth`; I opened its full signature. It takes a fixed
  complex and allowable-prime torsion cohomology, so does not state this target's
  coefficient-ring hypothesis and functor-level conclusion.

No mismatch was found, and no Lean or node content was changed. The five numbered
proof-docstring steps match the node's five steps; the only proof is `sorry`, with no
hollow definitions, private notions, local notation, or additional declarations.
The node's `lean.statement` is verbatim the module signature. The required server
`scompile.py NI nt-target-etale-smooth-ring` compiled the delivered module cleanly
(no errors or warnings).
