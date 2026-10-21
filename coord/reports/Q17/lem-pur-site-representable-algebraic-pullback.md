## Worker report

Item: lem-pur-site-representable-algebraic-pullback. The delivery states
`CategoryTheory.siteRepresentableAlgebraicPullback`, with proof `sorry`, in
`Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`. Its only helper is
`CategoryTheory.siteRepresentableArrowMap`: the existing `uliftYonedaMap`, viewed
as a morphism in the full category of sheaves using `ObjectProperty.homMk`.
There is no new construction of an inverse image, represented sheaf, natural
representable isomorphism, group object, or finite-limit comparison.

Sources read: Stacks `sites.tex`, Tag 04D3,
`lemma-pullback-representable-sheaf`, lines 2618–2630; the item's five expanded
proof steps; and the main-20261015 blueprint
`sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`,
the Roots of unity paragraph. The module docstring records the five proof steps.
The node's statement, dependency lists, and proof are unchanged. No repair note
for this item is present. No disputed mathematical assertion was found.

Hypotheses and their Lean rendering:

- The sites are `C : Type v₁`, `D : Type v₂`, with `Category.{u}` structures and
  topologies `J` and `K`. This is Mathlib's saturated site encoding; for the
  recorded covering-site definition the corresponding topologies are
  `Precoverage.toGrothendieck`. Sheaves and their morphisms are Mathlib's full
  subcategories `Sheaf J` and `Sheaf K`. No special property of a chosen basis of
  coverings is used by this item.
- Smallness relative to the coefficient universe is expressed by using sets in
  `Type (max u v₁ v₂ w)`. Thus the coefficient universe contains both object
  types and their hom types; the two object universes remain independent. The
  `uliftYoneda` lift uses that same bound and is equivalent sectionwise to Hom.
  There is no `Small.{u} C` or `Small.{u} D` assumption. The common hom bound is
  the common small universe of the recorded site inverse-image dependency.
- Finite limits of both sites are `[HasFiniteLimits C] [HasFiniteLimits D]`.
- Subcanonicity is `[J.Subcanonical] [K.Subcanonical]`, precisely saying that
  all represented set presheaves are sheaves, and furnishing `J.uliftYoneda`
  and `K.uliftYoneda`.
- The functor is `U : C ⥤ D`; `[PreservesFiniteLimits U]` is its finite-limit
  hypothesis. Covering preservation is expressed as `[U.IsContinuous J K]`.
  These are equivalent in this context, rather than separate assumptions:
  Mathlib `Functor.isContinuous_iff_coverPreserving` in
  `CategoryTheory/Sites/CoverPreserving.lean`, lines 190–193, applies because a
  finite-limit-preserving functor is representably flat (`flat_of_preservesFiniteLimits`).
  `CoverPreserving J K U` means that every covering sieve is pushed to a covering
  sieve. Thus this does not omit the covering hypothesis or impose a stronger one.
- `L` is the given geometric inverse-image functor on those set-sheaf categories,
  `adj` is its adjunction with the exact precomposition pushforward
  `U.sheafPushforwardContinuous`, and `[PreservesFiniteLimits L]` records the
  left exactness already specified by “geometric inverse-image adjunction”. No
  extra exactness, monoidal, or colimit hypothesis is imposed on L.

Clauses and their Lean rendering:

- Write `c_V` for `adj.uliftYonedaCompIso.hom.app V`, using the existing upstream
  natural isomorphism. The first conjunct states its `IsIso` property and, more
  importantly, `adj.homEquiv _ _ c_V = siteRepresentableArrowMap J K U V`.
  Adjunction bijectivity identifies this exactly with the node's definition of
  c_V as the adjunct of beta_V; it does not leave an arbitrary isomorphism.
- The formula beta_V(W)(a) = U(a) is the final quantifier over `W` and `a` in
  the first conjunct. The identity-section formula is explicitly the preceding
  equality at `op V` and `ULift.up (𝟙 V)`, with value `ULift.up (𝟙 (U.obj V))`.
  The lifts merely encode the universe transport on both sides.
- The second conjunct, quantified over every `a : V ⟶ V'`, is exactly
  `L.map (J.uliftYoneda.map a) ≫ c_V' = c_V ≫ K.uliftYoneda.map (U.map a)`.
  The Lean composition order agrees with the displayed equation of the node.
  The existing `adj.uliftYonedaCompIso` also gives the isomorphism of every
  represented diagram by whiskering; no arbitrary component family is used.
- The third conjunct quantifies over `I : Type z`, `SmallCategory I`,
  `FinCategory I`, and every diagram `V : I ⥤ C`. It states that the canonical
  comparison `preservesLimitIso` for `J.uliftYoneda ⋙ L`, followed by the map on
  limits induced by the components c, equals c at `limit V` followed by the
  comparison for `U ⋙ K.uliftYoneda`. This is precisely compatibility under the
  canonical finite-limit comparisons. Every other limiting cone is uniquely
  isomorphic to the chosen one, so this states the cone clause without choosing
  additional cone data. It includes the empty diagram, not just nonempty products.
- The fourth conjunct uses Mathlib's actual internal group objects `Grp C`.
  The `CartesianMonoidalCategory` binders encode choices of terminal objects and
  binary products; they exist by `CartesianMonoidalCategory.ofHasFiniteProducts`
  for C and for the sheaf category. The two functor `Monoidal` structures exist
  by `Functor.Monoidal.ofChosenFiniteProducts`, since both composites preserve
  finite limits. These choices are not extra hypotheses on the sites, functors,
  or represented groups, and the statement quantifies over all of them. On a
  cartesian monoidal category the functor monoidal structure is unique.
- `mapGrp` uses the canonical product and terminal comparisons to transport
  multiplication and unit, and sends inverse to the functor image of inverse
  (`Functor.grpObjObj`). Hence the existential natural isomorphism e in `Grp`
  states preservation of all three operations and the group identities. Both
  its forward and inverse underlying sheaf maps are fixed by explicit equalities
  to `adj.uliftYonedaCompIso.hom/inv.app G.X`. Naturality of e is compatibility
  with EVERY internal group homomorphism, including power maps when these are
  homomorphisms. No commutativity assumption is added.

Dependencies read and used:

- `def-weil-size-convention`: its recorded `lean` explicitly says this is a
  universe convention with no declaration or module. The explicit bound and
  universe-polymorphic finite shape above implement it.
- `def-weil-pbc-sites-and-cohomology`: imported
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, declaration
  `CategoryTheory.Precoverage.IsSiteForCoverings`, read its full definition and
  source docstring. As its `lean.note` specifies, the other components retain
  Mathlib `Precoverage.toGrothendieck` and `Sheaf`. This statement uses those
  general set-sheaf components, not abelian cohomology.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`: imported and read
  `Sheaf.CategoryTheory.SiteInverseImageTensor`,
  `CategoryTheory.siteInverseImage_tensor` and `siteInverseImage_tensor_coherence`.
  The supplied geometric adjunction and its left exactness are the interface
  required here. This lemma does not reconstruct that adjunction, tensor product,
  or their coherence and does not need the precoverage-specific construction
  hypotheses again after the geometric adjunction is given.
- `lem-galois-yoneda-hom-bijection` is the Mathlib leaf
  `CategoryTheory.yonedaEquiv`, read with `yonedaEquiv_naturality` and
  `yonedaEquiv_comp` in `Mathlib.CategoryTheory.Yoneda`, lines 724–760.
  The module imports that proof dependency. Its sheaf/universe-lift forms are
  `GrothendieckTopology.uliftYonedaEquiv` in `Mathlib.CategoryTheory.Sites.Subcanonical`.
- Reused the FULL existing signatures and proof of
  `CategoryTheory.Adjunction.uliftYonedaCompIso`,
  `uliftYonedaCompHom`, and its naturality lemma, in
  `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda`.
  Although located under algebraic geometry, these declarations are generic for
  arbitrary sites and arbitrary left adjoints of precomposition. This supplies
  the natural representable isomorphism, but does not state the item's normalized
  adjunct, finite-limit comparison equation, and full group-sheaf conclusion.
- Read `Functor.mapGrp`, `mapGrpNatIso`, `GrpObj`, `Grp`, and group morphism
  constructors in `Mathlib.CategoryTheory.Monoidal.Grp`; `preservesLimitIso` in
  `Mathlib.CategoryTheory.Limits.Preserves.Limits`; and the `uliftYoneda`
  limit-preservation instance in `Mathlib.CategoryTheory.Sites.PreservesLimits`.

Edge cases checked in the source-level statement:

- The identity site functor is permitted, as is any specified adjunction for its
  precomposition functor: normalization forces the comparison belonging to that
  adjunction, so no unjustified equality for an arbitrary adjunction is asserted.
- The terminal category/site is permitted. A finite-limit category cannot be empty;
  no extra nonemptiness requirement is introduced.
- The empty finite diagram is permitted (`FinCategory` has no nonempty premise).
  Its comparison is the terminal-object comparison; thus unit preservation is
  included. Binary products, equalizers, and arbitrary finite diagrams are covered.
- The trivial group and nonabelian group objects are permitted, and the isomorphism
  is natural for all group homomorphisms. No exponent, torsion, or characteristic
  restriction is present. No fullness or faithfulness of U is assumed.
- Independent object universes and an arbitrary finite-shape universe are retained;
  every variable/universe is bound, and `autoImplicit` is explicitly false.

Searches actually run:

- `msearch.py` LeanFinder: “The adjunct of the functor action on represented
  sheaves is a natural isomorphism compatible with finite limit cones and group
  objects”. Eight hits about adjunctions and sheaf inclusion, no complete match.
- `msearch.py` Loogle: `sheafPullback, yoneda`: zero hits; Loogle reported unknown
  identifier `sheafPullback`. This was not treated as proof of nonexistence.
- `msearch.py` grep in Mathlib CategoryTheory:
  `sheafPullback.*[Yy]oneda|[Yy]oneda.*sheafPullback|representable.*[Pp]ullback`.
  Eight unrelated classifier/representable-morphism hits, no complete match.
- `msearch.py` LeanSearch: “The canonical adjunct of the map on representable
  sheaves is an isomorphism natural in group objects and commuting with finite
  limit comparison isomorphisms”. Eight hits: represented group objects,
  `Adjunction.mapGrp`, and sheaf Yoneda; no complete match.
- `msearch.py` Loogle: `"mapGrpNatIso"`. Three exact hits: the lift of natural
  isomorphisms to group objects and its forward/inverse underlying-map formulas.
  These are used as the group API rather than introducing another group notion.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `sheafPullback.*[Yy]oneda|[Yy]oneda.*sheafPullback|pullback.*[Rr]epresentable`,
  then `uliftYoneda.*[Ii]so|[Ii]so.*uliftYoneda`: found the generic existing
  `Adjunction.uliftYonedaCompIso` via `FiniteLocallyConstantEtale/PullbackYoneda`.
  The project small-etale normalization module is a specialization, not this
  generic finite-limit and group-object statement. Read that module too.
- `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the two new declaration names: no clashes.

Only the helper definition has real data; the single new theorem is `sorry`.
The node copy changes only `lean`, listing both declarations and recording the
main theorem signature verbatim. No new nodes or dependency modules are needed.
Compilation and delivery preflight are performed by the prescribed wrappers.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
