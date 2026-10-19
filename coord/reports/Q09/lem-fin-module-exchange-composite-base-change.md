## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange` states
`AlgebraicGeometry.Etale.moduleExchange_composite_baseChange`, with `sorry` as its whole
proof. It includes the real construction `moduleInverseImageCompIso`, exactly the
`c^Λ_{a,b}` introduced in this node. No new DAG node, dependency repair, statement correction,
or source mutation is needed. The existing node's status is preserved verbatim.

The source was read in both snapshots: master
`sec-smooth-purity/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.md` and main-20261015
`sec-six-functors-basics/sk-prop-sf-cbc/lem-fin-radicial-exchange-descent.proof.md`, at the
sentence invoking compatibility with composition. The unbounded module formula is the
node's explicit version of that invocation. The module docstring also identifies the
formal exchange references, Stacks Tags 07A7 and 0E46. The statement docstring supplies a
full proof plan: sheaf square-comparison pasting, termwise passage to complexes, descent
along quasi-isomorphisms, horizontal pasting of mates, and cancellation of outside isos.
The node's proof and proof-dependency lists are empty; they are unchanged.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`.
  This is the recorded six-functor size convention; the scheme universe is `u` and module
  coefficients and sheaves have size `u + 1`. There is no finiteness, torsion, nonzero-ring,
  or boundedness hypothesis.
- The six schemes are `{X X₁ X₂ Y Y₁ Y₂ : Scheme.{u}}`; `f`, `f₁`, `f₂`, `g`, `g₁`, `k`,
  and `k₁` have exactly the seven types in the node.
- `sq₁ : ChosenCartesianSquare g₁ f₁ f g` and
  `sq₂ : ChosenCartesianSquare k₁ f₂ f₁ k` include both Cartesian identifications and
  both commutativity equations, using the dependency's structure. Their underlying
  outer rectangle is `sq₂.toCommSq.horiz_comp sq₁.toCommSq`, with top `k₁ ≫ g₁` and
  bottom `k ≫ g`. It is Cartesian by pullback pasting; the statement does not add that
  already implied fact as a tautological conjunct or require an independently chosen
  outer square.
- Module derived categories are the recorded `DerivedCategoryModule Λ X` and the
  definitionally identical `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat Λ))`
  behind the functors. `D(upperStar (ModuleCat.{u + 1} Λ) a)` is exact termwise inverse
  image; `R(lowerStar (ModuleCat.{u + 1} Λ) f)` is total right derived direct image.
- `moduleInverseImageCompIso Λ a b` is the inverse of
  `Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) b a) ≪≫
  Functor.mapDerivedCategoryCompIso _ _`. Thus it is precisely the localization descent
  of `c_{a,b}` and points from sequential inverse images to inverse image of the composite.
  Its data is composed from existing canonical isomorphisms, without a chosen arbitrary
  map or a postponed existence proof.
- Every exchange in the statement is the recorded `exactDerivedBaseChangeMap` on the
  appropriate square, specialized to `ModuleCat.{u + 1} Λ`. Its defining mate uses the
  canonical derived adjunction and the exact descended square comparison. The alternate
  base-change notation of `sbc-def-base-change-map` names the same exchange on an
  exchanged square; its recorded module is imported, rather than redefining that map.
- The first conjunct is equality of natural transformations, not just of components.
  Its four nonidentity factors in Lean composition order are: `whiskerLeft Rf_* c.inv`,
  `whiskerRight Ex_sq₁ D(k*)`, `whiskerLeft D(g₁*) Ex_sq₂`, and
  `whiskerRight c.hom Rf₂*`. The three functor associators supply parenthesization.
  These are exactly the four displayed arrows, in the displayed order; Lean's `≫`
  follows application order and scheme `k ≫ g` denotes the node's `g ∘ k`.
- The second conjunct quantifies `∀ K : DerivedCategoryModule Λ X` and says `IsIso` of
  the outer exchange component iff `IsIso` of
  `D(k*).map (Ex_sq₁.app K) ≫ Ex_sq₂.app (D(g₁*).obj K)`.
  It asks only for invertibility of that composite, not invertibility of both factors.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  full structure signatures and docstrings were read in the pinned source.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, its inherited `toCommSq`, and chosen
  pullback-identification/projection fields.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`:
  `CategoryTheory.IsPullback.paste_vert_iff` (the recorded Mathlib match), together with
  its horizontal specialization `paste_horiz_iff` and `paste_horiz`; these explain why
  the given rectangle is Cartesian. The exchange only needs its underlying `CommSq`.
  This module is imported through `ChosenCartesianSquare`'s `Mathlib...Pullbacks` import.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  the recorded `AlgebraicGeometry.Etale.DerivedCategoryModule` abbreviation and its
  standard sheaf-of-ModuleCat realization. This current source was read with
  `scompile.py --source` because it is absent from the older checkout.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, including its canonical module
  action, scalar transport, exactness and adjunction clauses. Its whole signature and
  docstring were read with `scompile.py --source`. The exact functor specialization
  used here is the dependency's recorded six-functor encoding.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `AlgebraicGeometry.Etale.exactDerivedSquareUpperStarIso` and
  `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap`; their full definitions were read.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`: the recorded
  `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow` and the imported module-valued
  `AlgebraicGeometry.Etale.derivedBaseChangeMap` are retained as the alternate convention.
  They introduce no new object or additional hypothesis in this statement.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStarComp` and `upperStarComp`. Their docstrings and full
  signatures show that `upperStarComp` has the opposite direction to the node's c;
  taking its inverse after descent is essential. This module is a public dependency
  of `ExactUnboundedExchange` through derived upper/lower star.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
  `mapDerivedUpperStarLowerStarAdjunction` and the notation `R` for its canonical
  derived direct image; its full defining signature was read.

Edge cases checked before drafting: empty schemes, identities in either base-change
step, zero complexes, the zero coefficient ring, arbitrary commutative rings including
positive characteristic, and complexes unbounded in both directions. All remain allowed.
The middle composite can be invertible without its factors individually being invertible;
the iff correctly tests the composite. Chosen pullback models need not be literal Mathlib
pullbacks. No extra Cartesian hypothesis is imposed on the already pasted rectangle.
No `let`, hidden local notation, private helper, or auto-bound universe is used.
No statement dispute or mathematical node fault was found.

Searches (2026-10-17):

- `msearch.py ... leanfinder "module-valued exchange composite cartesian square derived
  categories"`: eight unrelated Ext/localization hits; no etale exchange pasting.
- `msearch.py ... leansearch "derived exchange pastes under composite base change"`:
  eight hits on ring-theoretic base change, morphism properties and model categories;
  no matching theorem.
- `msearch.py ... loogle "mateEquiv_hcomp, upperStarComp, mapDerivedCategoryCompIso"`:
  zero hits, reporting unknown identifier `mateEquiv_hcomp`.
- `msearch.py ... grep "mateEquiv_hcomp|BaseChange.*paste|baseChange.*comp"
  CategoryTheory`: generic mate pasting in `CategoryTheory/Adjunction/Mates.lean` and
  bicategory mates, plus unrelated morphism-property declarations. These do not state
  the scheme/module/unbounded formula.
- Direct `rg` of upstream `WeilConjectures/` and shared `lean/Sheaf/` for
  `exactDerivedBaseChangeMap`, `derivedBaseChangeMapPlus_paste_horiz`, composition of
  exchange, and related pasting names: the existing horizontal derived pasting theorem
  is on `DerivedCategory.Plus`, not the required unbounded categories. Read its full
  signature in `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal`.
  `Sheaf.Paper.ExchangeIdentityPasting` also states only the bounded-below version.
  Scheme O-module pasting is a different coefficient/site theory.
- Direct upstream search for the item id found no declaration. Searches of Mathlib,
  upstream, shared Lean and `dag/lean_names_upstream.json` for the new declaration names
  found no duplicates. The wrapper source read resolved current dependency modules.

Validation: `scompile.py Q09 lem-fin-module-exchange-composite-base-change
lean/Sheaf/AlgebraicGeometry/ModuleExchangeCompositeBaseChange.lean` succeeded for both
sandbox and library module paths (2.5 s and 2.7 s), with no errors or non-sorry warnings.

## Second reading by Q09

This is the author's separate second pass, not an independent reviewer; the dispatch
brief assigns the independent delivery review to the maintainer and forbids sub-agents.
With the JSON node and the complete Lean file open, I rechecked all seven morphism types,
both chosen Cartesian hypotheses, the outer rectangle's orientation, and the source and
target of each of the four factors. The source of the equality is
`Rf_* ⋙ D((k ≫ g)*)`, its target is `D((k₁ ≫ g₁)*) ⋙ Rf₂*`, so both are functors from
D(X_et,Λ) to D(Y₂_et,Λ). Inverting `upperStarComp` in the helper makes c point in exactly
the direction named by the node; its inverse is used on the bottom composite and its
hom on the top composite, as required. Associators carry no additional content.
The second conjunct retains every unbounded K and uses the middle two-factor component
only; no hypothesis that either exchange is individually invertible has appeared.
The recorded canonical maps and coefficient category were retained. No mismatch was
found and no change was needed in this second pass.
