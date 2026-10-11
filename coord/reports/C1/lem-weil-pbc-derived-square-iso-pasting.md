## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting` states the three derived
laws as `AlgebraicGeometry.Etale.derivedSquareIsoPasting` and the final sheaf-level
clause as `AlgebraicGeometry.Etale.sheafSquareIsoPasting`. Both proofs are `sorry`;
there are no new definitions and no statement correction.

Source read: Stacks Remarks [0E46](https://stacks.math.columbia.edu/tag/0E46) and
[0E47](https://stacks.math.columbia.edu/tag/0E47), online because the local literature
checkout is absent. The remarks give vertical and horizontal pasting of base change;
the node isolates the coherence of the inverse-image square identifications used there.
The identity clause is the unit coherence described in the node's proof.

Hypothesis and clause dictionary (applies to both declarations):

- All eight schemes and all nine arrows are explicitly bound, in arbitrary universe u.
  The node's first square is `sq₁ : IsPullback g' f' f g`, its second is
  `sq₂ : IsPullback h' f'' f' h`, and its third is `sq₃ : IsPullback g'' e' e g'`.
  `IsPullback` gives the commutativity and fibre-product universal property; equivalently
  it gives the specified comparison with the chosen scheme pullback. The comparison
  depends only on `.toCommSq`, so no choice of the identification alpha is lost.
- `A := AddCommGrpCat.{u + 1}` renders abelian etale sheaves. In the first declaration,
  `P q := (upperStar A q).mapDerivedCategoryPlus` is the bounded-below inverse image.
  In the second, `P q := upperStar A q` is the sheaf inverse image.
- `θ` is respectively `pullbackSquareComparison A` or `squareUpperStarIso A`.
  `c` is the inverse of `upperStarCompDerivedPlus A` or `upperStarComp A`, matching
  the node's orientation from successive inverse images to the composite inverse image.
  `i` is respectively `upperStarIdDerivedPlus A` or `upperStarId A`.
- The first conjunct evaluates theta for `(IsPullback.id_horiz f).toCommSq` at K.
  Its right side is `P f` applied to `i Y`.hom, followed by `i X`.inv at `P f K`:
  exactly the identity-square formula.
- The second conjunct's left side is `P f''` applied to `c h g`.hom, followed by
  theta of `sq₂.paste_horiz sq₁`. Its right side is theta of sq₂ at `P g K`, followed
  by `P h'` of theta of sq₁, followed by `c h' g'`.hom at `P f K`. This is (2),
  in Lean's diagrammatic order of composition.
- The third conjunct's left side is `c e' f'`.hom at `P g K`, followed by theta of
  `sq₃.paste_vert sq₁`. Its right side is `P e'` of theta of sq₁, theta of sq₃ at
  `P f K`, and `P g''` of `c e f`.hom. This is (3).
- `∀ K` ranges over all of the relevant sheaf or bounded-below derived category.
  Equality of all components is equivalent to equality of natural transformations,
  hence of the natural isomorphisms in clause (1). The three configurations share
  binders for compactness; any unused extra square can be taken to be an identity
  square, so this does not add a hypothesis to any individual law.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.squareUpperStarIso` (def-weil-pbc-cartesian-square).
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`:
  `AlgebraicGeometry.Etale.pullbackSquareComparison` (def-weil-pbc-derived-square-iso).
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`:
  `AlgebraicGeometry.Etale.derivedInverseImageComposition`; the statement's existing
  cD/eD are `upperStarCompDerivedPlus` and `upperStarIdDerivedPlus` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, whose full
  defining signatures and factorization-characterization docstrings were read.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and `.Coherence`:
  `upperStarComp`, `upperStarId` (lem-weil-pbc-inverse-image-composition).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`:
  `CategoryTheory.IsPullback.paste_vert_iff` (lem-weil-pbc-cartesian-square-pasting);
  the forward pasting constructors `paste_vert` and `paste_horiz` form the rectangles.

Edge cases checked: no nonemptiness, finite type, properness, characteristic, or
nonzero-object assumption is imposed. Empty schemes and zero sheaves/complexes are
included. All arrows may be identities. Schemes have arbitrary universe u and the
coefficient category has the usual u+1 size of the recorded dependencies.
The node has no numerical index or boundedness bound to restrict.

Searches made:

- msearch LeanFinder: "identity and horizontal and vertical pasting laws for the derived
  inverse image square isomorphism of etale sheaves"; eight unrelated restriction
  functor/open immersion hits, no exact derived square law.
- msearch Loogle: "AlgebraicGeometry.Etale.pullbackSquareComparison,
  AlgebraicGeometry.Etale.upperStarCompDerivedPlus"; no hits, upstream identifier unknown
  to the public Loogle index.
- msearch grep: `pullbackSquareComparison|squareUpperStarIso|paste_horiz|paste_vert`
  in Mathlib CategoryTheory; 25 ordinary pullback-pasting hits, no etale derived law.
- msearch LeanSearch: "pasting coherence of natural isomorphisms of inverse image
  functors on derived categories"; unavailable, Internal Server Error. No verdict
  inferred from the unavailable search.
- rg over WeilConjectures and lean/Sheaf for `squareUpperStarIso_(paste|id)`,
  `pullbackSquareComparison`, `CommSq.*paste`, `paste_horiz`: the source has the
  sheaf laws in BaseChange/Pasting and DerivedPasting, and derived base-change-map
  laws, but no derived square-comparison laws. Read their signatures to distinguish
  these. No existing Sheaf module supplies this item.
- rg for the item id and the proposed declaration names in WeilConjectures and
  dag/lean_names_upstream.json: no matches.

Server compilation: both declarations compile together cleanly in 3.9 seconds,
without warnings. Initial drafts were replaced by component formulas to avoid costly
functor-association elaboration; the final file has no increased heartbeat option.

## Second reading by C1

I reread the node statement, its source place (Stacks Remarks 0E46 and 0E47),
the dependency signatures, and `DerivedSquareIsoPasting.lean` item by item.

- Objects and hypotheses: the Lean binders `{X Y X' Y' X'' Y'' W W' : Scheme.{u}}`,
  the nine morphisms `f, f', g, g', f'', h, h', e, e', g''`, and
  `sq₁ : IsPullback g' f' f g`, `sq₂ : IsPullback h' f'' f' h`,
  `sq₃ : IsPullback g'' e' e g'` render exactly the schemes, arrows, and three
  cartesian squares in the node. No extra geometric, finiteness, characteristic,
  or nonzero hypotheses occur.
- The derived clause introduces `A := AddCommGrpCat.{u + 1}`,
  `P q := (upperStar A q).mapDerivedCategoryPlus`,
  `θ := pullbackSquareComparison A`,
  `c := (upperStarCompDerivedPlus A).symm`, and
  `i := upperStarIdDerivedPlus A`; `∀ K : DerivedCategory.Plus ...` is the
  node's quantification over every bounded-below derived object. The three
  conjuncts render identity, horizontal pasting, and vertical pasting in that
  order. Every whiskering and composition has the node's orientation and the
  same source and target (the displayed `≫` order is Lean's categorical order).
- The sheaf clause repeats the same three laws with
  `P q := upperStar A q`, `θ := squareUpperStarIso A`,
  `c := (upperStarComp A).symm`, `i := upperStarId A`, and
  `∀ K : Sheaf Y.smallEtaleTopology A`, exactly as required by the final node
  sentence. No quantifier or conclusion clause is missing or strengthened.

Edge cases are covered: the universe `u` is arbitrary; identity arrows and
empty schemes are allowed; all sheaves/complexes, including the zero object,
are quantified; there is no index, characteristic, boundedness bound beyond
`D+`, or nonemptiness assumption.

Searches were repeated with LeanFinder/Loogle and grep over Mathlib,
`WeilConjectures`, and `lean/Sheaf` for the item and the declarations
`derivedSquareIsoPasting`, `sheafSquareIsoPasting`, and the relevant pasting
identifiers. They found only generic pullback-pasting and the separate
sheaf-level laws; no existing declaration states this derived theorem. The
worker's unavailable LeanSearch result is recorded in the worker report.

No mismatch was found, so no source, node, or Lean change was necessary. The
module compiled cleanly with `scompile.py`; both declarations remain statement
only (`sorry`) and carry the source and blueprint docstrings.

## Reviewer fix (R-dsp1023, stage 2)

- `sheafSquareIsoPasting` removed: it restated the source lemmas `AlgebraicGeometry.Etale.squareUpperStarIso_id`,
  `squareUpperStarIso_paste_horiz_hom`, `squareUpperStarIso_paste_vert_hom` (WeilConjectures.SixFunctors.BaseChange.Pasting /
  .DerivedPasting), already recorded on node lem-weil-pbc-square-iso-pasting (one declaration per notion, H4). The node's
  closing sheaf-level sentence is that node's existing statement; the module docstring says so.
- `derivedSquareIsoPasting` restructured: the three laws are now three conjuncts each binding only its own squares
  (identity: `f`, K; horizontal: sq₁, sq₂, K; vertical: sq₁, sq₃, K) instead of one shared binder list that made the
  identity law carry three unused cartesian squares. The formulas themselves are unchanged and were checked against the
  node (orientation of `pullbackSquareComparison`, `upperStarCompDerivedPlus`, `paste_horiz`/`paste_vert`, `id_horiz`).
