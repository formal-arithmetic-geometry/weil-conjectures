## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceChangeBase` states
`AlgebraicGeometry.AlgebraicSpace.exists_spaceChangeBase`, with its sole proof
`sorry`. The node is unchanged except for `lean`. There are no new definitions,
new nodes, dependency repairs, or statement corrections.

The theorem uses an existential extension functor characterized by its complete
section formula, rather than choosing an uncharacterized object or map. This is
also the format of the existing localized-sheaf prerequisite. All the data in the
conclusion are tied to that same functor and those same section identifications.
In particular the equivalence of étale sites is normalized on its chart maps,
and the identification of rings is the actual scheme pullback on regular
functions. No mere existence of an unrelated equivalence replaces these clauses.

Hypotheses and clauses, in statement order:

- A morphism of arbitrary schemes is `{S S' : Scheme.{u}} (g : S ⟶ S')`.
  The explicit universe `u` is the existing algebraic-space framework's universe
  of schemes and section sets. Its scheme category has objects in `Type (u+1)`
  and morphisms in `Type u`. No small-category assumption or equality of these
  object and morphism universes is imposed. The metatheoretic size-convention
  node introduces no additional mathematical datum. The case `Spec Z` is included
  without restricting the arbitrary smaller base.
- `X` ranges over the recorded `AlgebraicSpace S`, so its given fppf sheaf,
  representable diagonal and existence of a scheme atlas are retained.
- `J : AlgebraicSpace S ⥤ Over (schemeSpace (Over.mk g))` simultaneously
  provides the extended algebraic space and its canonical morphism to `h_S`.
  Thus algebraicity in clause (1) is present in the type of `(J.obj X).left`.
  The codomain is exactly the category of pairs in clause (2), including the
  commuting-triangle condition on arrows, provided by `Over`.
- `e X T` identifies its sections with
  `Σ a : T ⟶ Over.mk g, X.obj.obj.obj (op (Over.mk a.left))`.
  An arrow `a` in `Over S'` is precisely a map `phi : T.left ⟶ S`
  satisfying `phi ≫ g = T.hom`, so this is the displayed disjoint union in
  the node. It is the actual sheaf's sections, without an additional
  sheafification map or a weakened locally-defined formula.
- The first conjunct says the map to `h_S` is exactly the first projection
  under `e`. The next conjunct is the evident restriction formula
  `(a,s) ↦ (b ≫ a, X(b.left)(s))` along every arrow `b` of the base site.
  The following conjunct specifies the action on every space morphism
  `f : X ⟶ Y` as `(a,s) ↦ (a,f(s))`. These formulas fix the extension
  as a functor, not merely its objectwise isomorphism class without maps.
- `J.IsEquivalence` states precisely that this very functor to the pair
  category is an equivalence. It supplies both essential surjectivity and
  the full morphism comparison; it is not just an objectwise assertion.
- For every given scheme `U : Over S` and map `a : yoneda.obj U ⟶ X.obj.obj`,
  the assumptions `IsEtale a → IsSurjective a` express the specified atlas.
  The witness `b` has source `yoneda.obj ((Over.map g).obj U)`, hence exactly
  the same scheme with its composite map to `S'`. Its section on the identity
  is prescribed by `e` to be `(U.hom, a(id_U))`. Yoneda and the restriction
  formula then prescribe all of its components, so this is the given atlas
  viewed over the smaller base. `IsEtale b ∧ IsSurjective b` is its asserted
  preservation. The identity map occurring inside the formula
  `Over.mk U.hom ⟶ U` only converts the record presentation of the same
  scheme over `S`; it is not an added hypothesis.
- For every square of algebraic spaces `P,A,B,C`, with arbitrary arrows
  `p,q,f,h`, the `IsPullback` implication preserves the sheaf pullback square,
  including both specified projections. By the recorded
  `fibreProduct_isAlgebraicSpace`, the sheaf fibre product in the node can be
  used as `P`. The conclusion then says its canonical comparison with the
  target sheaf fibre product is an isomorphism. Preservation of squares is
  the equivalent universal-property formulation of the canonical-iso clause,
  with the same middle object, not a product over an unrelated base.
- For each `X`, `E : X.EtaleSite ≌ (J.obj X).left.EtaleSite` compares the
  recorded small étale sites. Its natural isomorphism `a` of functors to
  `Over S'` identifies the underlying scheme chart and every scheme arrow
  with its original chart viewed over `S'`. The chart equation after `a`
  requires the chart's section, transported by `a.inv`, to have exactly
  the original map to `S` and section under `e`. Thus `E` is the chart
  correspondence induced by extension, rather than an arbitrary abstract
  category equivalence.
- The quantified presieve equivalence says exactly that a family covers
  before extension if and only if its image under `E.functor` covers.
  `etalePrecoverage` is the recorded jointly surjective étale precoverage;
  its generated topology is the recorded `etaleTopology`.
- The final isomorphism `r` identifies the original structure presheaf with
  `E.functor.op ⋙ (J.obj X).left.structurePresheaf`. Its component is required
  to equal `(forget₂ CommRingCat RingCat).map
  (Scheme.Γ.map (a.hom.app T).left.op)`, the canonical pullback of regular
  functions along the identified underlying scheme. Both presheaves are the
  recorded structure sheaves' underlying presheaves, so this is precisely
  the structure-sheaf identification, including restriction maps.
- Compatibility with `V ↦ V ×_Y X` for every `h : X ⟶ Y` is rendered by
  the universally quantified pullback-square clause together with the
  chart-normalized `E` and the action-on-morphisms formula. Use the square
  defining `V ×_Y X`, with `V` the scheme space of a chart: the two mapped
  projections are the given projections, and hence give the canonical
  comparison, naturally in every arrow of `V` by uniqueness in that same
  universal property. The chart equation identifies the image of `V`
  with precisely `V/S'`. When the fibre product is a scheme its chart is
  therefore carried to that same scheme fibre product. In general it is
  an algebraic space, and its representable étale projection has the same
  scheme tests `T ×_Y V`. This retains the nonrepresentable `h` case;
  it does not assert that all these fibre products are schemes. The ring
  component formula retains their same scheme pullbacks on functions.
- There is no finiteness, separation, representability, characteristic,
  nonemptiness, or smoothness assumption on `g`, `X`, or the space arrows.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; schemes are locally affine
  locally ringed spaces, and arrows are locally ringed space morphisms.
- `def-weil-size-convention`: its convention-only record; explicit universe
  `u` uses the dependency's existing size convention without introducing a
  new object or an extra category-size hypothesis.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology`, localized with `.over S`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace`, `IsEtale`, `IsSurjective`, `EtaleSite`,
  `etalePrecoverage`, `structurePresheaf`, and `structureSheaf`.
  No alternative space, chart, site, or structure-sheaf notion is defined.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `fibreProduct_isAlgebraicSpace`; its exact signature states the algebraicity
  and universal property of the sheaf pullback. Its other clauses
  `etaleCover_pullback` and `etale_fibreProduct_isScheme` were also read.
- `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, `schemeSpace` and
  `schemeSheaf_isAlgebraicSpace`. This is the actual Yoneda sheaf, with only
  its algebraic-space property supplied by the named theorem. Its module is
  public because the pair category in the statement uses `schemeSpace`.
- `lem-weil-pbc-localized-sheaves-over-representable`:
  `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`,
  `CategoryTheory.exists_localizedSheavesOverRepresentable_general`.
  Read its full sigma, projection, restriction and morphism formulas and
  the inverse-fibre formula. It is a generic sheaf equivalence on a small
  site, not the present algebraic-space result; it is a proof import.
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`:
  `Mathlib.CategoryTheory.Sites.Limits`, `Sheaf.createsLimitsOfShape` and
  `Sheaf.isSheaf_of_isLimit`, as the node's Mathlib match records. Proof import.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `Limits.pullback` and its two projections. Proof import. `IsPullback` is
  the existing square universal property, with no new notion introduced.

Sources read: `literature/stacks-project/spaces.tex`,
`lemma-change-base-scheme` (03I4), `definition-base-change` (03I5) and
`lemma-category-of-spaces-over-smaller-base-scheme` (04SG), including the
proofs; `spaces-properties.tex`, `lemma-2-morphism` (04KK), including its
first proof paragraph identifying the small ringed sites. The theorem
proof docstring gives all six steps of the node, including the correction
already made in stage 1 that a chart pullback need not itself be a scheme.

Edge cases checked before writing:

- Identity base map: each sigma has the unique possible map to the base;
  extension and the site comparison reduce to the identity up to the
  displayed canonical identifications.
- Empty schemes and empty spaces: sigma fibres may be empty; no
  nonempty-set hypothesis or choice of an atlas is added. An empty atlas
  and an empty covering remain allowed by the existing definitions.
- `S = Spec k ⊔ Spec k`, `S' = Spec k`: extension preserves a fibre product
  over the extended middle space, not a product over `S'`. The former can
  have two components while the latter has four. The stated square retains
  the correct middle space and both maps.
- Nonseparated schemes and spaces: the statement imposes no closedness on
  diagonals. The docstring uses the general scheme diagonal-test fibre
  product, not a closed-immersion argument.
- Nonrepresentable space morphism: with `Y = V = S`, the chart pullback
  is `X`, which need not be a scheme. The formulation uses sheaf pullback
  squares of algebraic spaces and does not exclude this case.
- Arbitrary characteristic and arbitrary `g`, including the structural map
  to the integers: no prime or finite-type hypotheses occur.

Searches (2026-10-24):

- `msearch.py`, LeanFinder: "extension of algebraic spaces to a smaller base
  scheme equivalence slice category etale sites". Eight hits including
  `Scheme.Etale.forget`, `Scheme.Etale.forgetFullyFaithful`, and
  `Scheme.CanonicallyOver`; all concern schemes, not algebraic-space extension.
- `msearch.py`, Loogle: `CategoryTheory.Over.iteratedSliceEquiv`. Nine hits
  give the slice-of-slice equivalence and its functor, inverse, unit and
  counit formulas; none establishes algebraicity or the ringed-site clause.
- `msearch.py`, Mathlib grep: `AlgebraicSpace|changeBaseScheme` in
  `AlgebraicGeometry`; zero hits.
- `msearch.py`, LeanSearch: "Viewing algebraic spaces over a smaller base
  scheme identifies the small etale ringed sites and preserves fibre
  products". Eight hits including `Scheme.smallEtaleTopology`,
  `Scheme.smallEtalePretopology`, and étale base-change stability; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `changeBase|change.base|baseForget|smaller.base|extensionPresheaf|jShriek|jshriek`
  found unrelated scheme base changes, open extension by zero, and proof
  docstrings referring to this still-unstated node. The exact node-id search
  in `lean/WeilConjectures` found no declaration.
- Additional `rg` for `changeBaseScheme|spaceChangeBase|smaller base|smaller.base.scheme`
  in both project roots found only unrelated comments. Searching
  `dag/lean_names_upstream.json` for the proposed declaration and
  `AlgebraicSpace` found no conflicting upstream declaration.

Validation: the server's sandbox and library-name compiles both passed,
with no errors or warnings, using `scompile.py` and the default 60-second
per-file limit. All variables and universe levels are explicit. The
sole postponed theorem is exactly the node's declaration. No
`STATEMENT-DISPUTED` flag or unresolved node fault is asserted.

## Second reading by Q86

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
