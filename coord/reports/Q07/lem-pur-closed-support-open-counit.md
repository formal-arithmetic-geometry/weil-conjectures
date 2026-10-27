## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedSupportOpenCounit` states
`AlgebraicGeometry.Etale.closedSupport_openCounit`, with its sole theorem proof
`sorry`. The two helper definitions `openCounitRestrictionLift` and
`closedSupportOpenCounitArrow` construct the actual arrows from the given
restriction isomorphism; neither chooses data from a postponed theorem.
No node statement, dependency list, proof, or other field changes.

Hypothesis and clause comparison:

- The commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]`.
  The schemes are `{Y U Z : Scheme.{u}}`. This is the existing size convention
  of the recorded ordinary etale module-sheaf and derived-category interfaces.
- The open immersion is `(j : U ⟶ Y) [IsOpenImmersion j]`. The closed immersion
  is `(i : Z ⟶ U) [IsClosedImmersion i]`, and closedness of the composite is
  separately required by `[IsClosedImmersion (i ≫ j)]`. Thus `k = j i` is
  represented by composition in Lean's forward order, `i ≫ j`.
- The arbitrary module sheaf is
  `B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)`.
  This is the six-functor encoding explicitly authorized in the dependency
  records for modules over the constant coefficient ring; there is no finiteness,
  torsion, characteristic, constructibility, or boundedness condition.
- `F` is the explicit term `(lowerStar (ModuleCat A) (i ≫ j)).obj B`;
  `G` is `(lowerStar (ModuleCat A) i).obj B`. They are never arbitrary sheaves
  supplied in place of the prescribed pushforwards.
- The existential `ρ` is an isomorphism from `upperStar j F` to `G`.
  Its first conjunct normalizes every section component. For every `V : U.Etale`,
  the isomorphism `τ` lies in `Z.Etale` from `V ×_U Z` to `V ×_Y Z`.
  A morphism in this category commutes with the projection to `Z`; the displayed
  equality with `pullback.fst` also fixes its projection to `V`. Hence the
  pullback universal property uniquely fixes `τ`: it is the canonical
  fibre-product identification, not an arbitrary change of coordinates.
  After the published `upperStarIsoOpenImmersionRestriction` comparison, the
  component of `ρ.hom` is exactly `B.obj.map τ.hom.op`. Since `B` is
  contravariant, this map has domain `B(V ×_Y Z)` and codomain `B(V ×_U Z)`.
  This is precisely the identity after canonical identification required by
  the node. These component equalities fix `ρ` uniquely.
- The second conjunct says `IsZero (F(T))` whenever the image of an etale
  `T → Y` is disjoint from `Set.range (i ≫ j)`. These are exactly the etale
  objects factoring through the open complement of the closed image of `k`.
  Thus this states that `F` restricts to zero on that complement, without
  selecting an extra open subscheme or assuming a stronger support condition.
- `openCounitRestrictionLift` is `ρ.inv` embedded in degree zero followed by
  the inverse of `upperStar.mapDerivedCategorySingleFunctor 0`. Its codomain
  is therefore the actual derived inverse image of degree-zero `F`.
- `closedSupportOpenCounitArrow` applies the actual exact derived `j_!` to this
  arrow and composes with the counit of
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`
  applied to `openImmersionLowerShriekUpperStarAdjunction`. This is the
  specified localization of the original sheaf adjunction, not a separately
  chosen adjunction or a merely isomorphic functor. The third conjunct is
  `IsIso` of this very arrow `e`.
- The final conjunct quantifies over every `M : DerivedCategoryModule A Y`
  and every derived `c : F[0] ⟶ M`. The expression mapped by derived `j_!`
  is `openCounitRestrictionLift ... ρ ≫ D(j⁻¹).map c`, precisely `c_U`.
  Its composite with the specified counit at `M` equals `e ≫ c`.
  Composition is written in forward order throughout. Taking `M` to be any
  degree-zero sheaf shifted by any integer yields the last clause of the
  node; no restriction on shifts is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded etale-sheaf
  vocabulary, with Mathlib `CategoryTheory.Sheaf` and `ModuleCat` for the
  six-functor constant-coefficient module encoding.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` and `upperStar`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, `upperStarIsoOpenImmersionRestriction`,
  `openImmersionLowerShriekUpperStarAdjunction`, and
  `preservesFiniteLimits_openImmersionLowerShriek`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, through its public
  imports: `AlgebraicGeometry.Etale.DerivedCategoryModule`;
  Mathlib `DerivedCategory.singleFunctor` and
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`, whose full
  definition localizes the termwise adjunction using the standard exact-functor
  factorizations, thereby fixing its units and counits.
- Proof imports preserve the recorded plan:
  `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
  (`AlgebraicGeometry.etaleInverseImageModulesExact`),
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
  (`openImmersionLowerShriekCompUliftSheafFiberIso`),
  `Sheaf.AlgebraicGeometry.PointedEtaleStalk` (`AlgebraicGeometry.pointedEtaleStalk`),
  and `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
  (`AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map`).

Sources opened: Stacks `etale-cohomology.tex` definition-extension-zero
(03S3), including its restriction and presheaf descriptions;
lemma-ses-associated-to-open (095L), including its stalkwise proof;
`derived.tex` lemma-right-derived-exact-functor (015F); and the current
blueprint `thm-pur-rank-one-thom.proof.md`, Step 2.
The theorem docstring reproduces all five proof steps, including the cofinal
pointed-neighbourhood argument inserted in the reviewed stage-1 node.

Edge cases checked before writing: `Z` empty, zero `B`, the zero coefficient
ring, empty `U` and `Y`, `j` the identity, etale test objects with empty source,
and unbounded derived targets and negative shifts. In each case the formulas
retain their usual meaning. Closedness of `k` is essential: with
`Z = U = G_m`, `Y = A^1`, `i` identity and `j` the open inclusion,
`j_*` of a nonzero constant sheaf has a nonzero stalk at the origin whereas
`j_!` has zero stalk. The theorem retains the hypothesis excluding that case.
No statement dispute or correction was needed. `autoImplicit` is disabled.

Searches made through the prescribed search wrapper:

- LeanFinder: "A closed immersion factoring through an open immersion has
  extension by zero of its pushforward isomorphic to the ambient pushforward
  via the actual derived counit". Eight hits, including
  `Scheme.Modules.restrictFunctorAdjCounitIso`, `restrictAdjunction`, and
  `restrictAdjunction_counit_app_app`. These concern Zariski structure-sheaf
  modules rather than ordinary etale constant-coefficient modules and do not
  give this statement.
- Loogle: `CategoryTheory.Adjunction.counit, "naturality"`. Two hits:
  `Adjunction.counit_naturality` and its reassociated variant. These supply the
  general formal calculation, not the closed-support reconstruction.
- Mathlib grep, `AlgebraicGeometry`:
  `extensionByZero|closed.*support.*counit`. No hits.
- LeanSearch: "For a closed immersion factoring through an open immersion the
  actual derived extension by zero counit on its direct image is an isomorphism".
  Eight hits concerning scheme images, Zariski restriction and stalks; none
  states this ordinary etale module theorem with its component normalization.
- Project grep of both `lean/WeilConjectures` and `lean/Sheaf`:
  `lem-pur-closed-support-open-counit|closedSupport|closed_support`.
  No item-tag match. Existing closed-support theorems concern pro-etale
  coefficients, complementary open/closed pairs, or exceptional comparisons.
  None gives this statement. Exact-name searches for all three delivered declarations
  in `dag/lean_names_upstream.json`, Mathlib and both project roots found no matches.
  The upstream open-immersion definition file
  supplies exactly the functors used here and is reused.

Validation: every delivered Lean file is compiled individually through
`scompile.py`; delivery preflight and dry run are performed through `deliver2.py`.
The stage-1 reviewed status is retained, and there is no repair note on this item.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
