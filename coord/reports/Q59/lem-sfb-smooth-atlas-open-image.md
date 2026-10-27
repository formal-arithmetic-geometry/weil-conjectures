## Worker report

States `CategoryTheory.smooth_atlas_open_image` in
`Sheaf.AlgebraicGeometry.SmoothAtlasOpenImage`. Its only proof is `sorry`.
The docstring carries all seven proof steps of the node, with their dependency ids.
Source read: literature/stacks-project/stacks-properties.tex,
lemma-open-image-substack (Tag 05UP), including the definition by surjectivity,
the two cartesian squares, the open image T_0, and the final atlas argument.
The node's scheme-atlas specialization of that algebraic-space-atlas lemma is unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The stack is
  `X : BasedCategory.{v, w} (Over S)` with `hX : IsAlgebraicModuliStack X`.
  This expands to etale stack descent, representable algebraic-space diagonal,
  and existence of a representable smooth surjective scheme atlas.
- `U V : Over S` are the two schemes with their structural maps.
  `p : BasedFunctor (discreteModuli (yoneda.obj U)) X` is the given map U to X.
  `hp : IsSmoothModuliAtlas X U p` asserts exactly the specified representability,
  smoothness, and surjectivity after every scheme test, with the projection retained.
- `j : V ⟶ U` and `hj : IsOpenImmersion j.left` are the open immersion.
  The actual composite is `(discreteModuliMap (yoneda.map j)).comp p` throughout.
- The first conjunct is `IsRepresentableByAlgebraicSpaces` of this composite.
  The second is `ModuliSpaceTest @Smooth` of the same composite: smoothness
  on every representable etale scheme chart after every scheme base change.
- `∃ W : OpenModuliSubstack X` gives the strictly full pullback-stable subcategory,
  with every scheme pullback represented by an actual open immersion.
  Pullback stability along every arrow also implies closure under isomorphisms.
- `q : BasedFunctor (discreteModuli (yoneda.obj V)) W.category` is the factor map.
  `IsAlgebraicModuliStack W.category` states its algebraicity, and
  `IsSmoothModuliAtlas W.category V q` states representable smooth surjectivity.
- `Nonempty (ModuliTwoIso (q.comp (fullModuliInclusion X W.property))
  ((discreteModuliMap (yoneda.map j)).comp p))` is the 2-commutative factorization.
  Equality of functors is not imposed on a 2-categorical assertion.
- For every `T : Over S` and `t : BasedFunctor (discreteModuli (yoneda.obj T)) X`,
  `Z`, `a`, and `HasSpaceBaseChange ... T t Z a` present V times_X T with its
  actual projection to T. `O`, `i`, and `e` present T times_X W;
  `IsOpenImmersion i.left`, `e.toFunctor.IsEquivalence` and the projection
  `ModuliTwoIso` make O an open subscheme representing precisely that pullback.
- The final `Set.range i.left = {x | ...}` says that its underlying open is the
  point image of `a`. The right side is the union, over all representable etale
  scheme charts `b : h_A → Z`, of the images of the actual scheme maps
  `(yoneda.preimage (b ≫ a)).left`. These charts cover Z; every algebraic-space
  point lifts to one after a field extension, and conversely every such scheme
  point maps to a point of Z. Thus this is exactly the algebraic-space point image
  in the ordinary underlying space of T. It uses the existing chart definition of
  `SpaceMapIsSurjective`, rather than defining a second notion of image or points.
- Empty V is allowed: no Nonempty, nonempty-image, quasi-compactness, finite-type,
  or Noetherian hypothesis is present. Independent v and w retain arbitrary total
  stack category universes; all test schemes are in the existing universe u.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids:
  `IsFibredInGroupoids`, `IsModuliStack`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`,
  `HasAlgebraicSpaceDiagonal`, `SpaceMapIsSurjective`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, with its actual presheaf pullback convention.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- Sheaf.AlgebraicGeometry.AlgebraicModuliStack: `SpaceMapIsSmooth`,
  `IsSmoothModuliAtlas`, `IsAlgebraicModuliStack`.
- Sheaf.AlgebraicGeometry.OpenModuliSubstack: `OpenModuliSubstack`, its `category`,
  and `fullModuliInclusion`.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `ModuliSpaceTest`.

The last three definition nodes already have usable landed records and are added
only to stmt_deps, as authorized for existing landed notions. No definitions or
other node records are changed. Proof imports are the recorded point/open calculus,
flat-lfp universal openness, chartwise smooth-etale calculus, and Mathlib Etale.
The open-factorization proof dependency is already imported publicly through
Mathlib OpenImmersion (`IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`).

Edge cases checked before drafting: V empty gives the empty open substack and
empty atlas; V=U gives all of X by surjectivity of p; T empty has empty range on
both sides; an empty X admits the corresponding empty atlas; disconnected or
non-quasi-compact U and V are unrestricted. The image need not be all of X when
V is a proper open, so q is required to be surjective only onto W.

Searches for reuse:

- msearch.py leanfinder: "The image of an open subscheme of a smooth atlas of an
  algebraic stack is an open substack with a smooth surjective atlas". Eight hits,
  only scheme smoothness/open-immersion results and smooth loci; no stack theorem.
- msearch.py leansearch: "A smooth atlas restricted to an open subscheme surjects
  smoothly onto an algebraic open substack". Eight hits on scheme restrictions,
  scheme smoothness and manifold atlases; no stack open-image theorem.
- msearch.py loogle: `"Stack", "IsOpenImmersion"`. Zero hits.
- msearch.py grep: `AlgebraicStack|open.image.substack|smooth.atlas`. Zero hits.
- rg in lean/WeilConjectures: `smooth.*atlas|open.image.substack|IsAlgebraicModuliStack|
  IsOpenModuliSubstack` and the exact item id. No matches.
- rg in lean/Sheaf/AlgebraicGeometry for the stack/open/atlas predicates found
  AlgebraicModuliStack, OpenModuliSubstack, DmStackMorphismProperties and
  StackChartwiseSmoothEtaleCalculus. Their full definitions were read and reused.
- rg in Mathlib, lean/WeilConjectures and lean/Sheaf for the new declaration name
  `smooth_atlas_open_image` found no existing declaration.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED issue.

Validation: scompile.py compiled both sandbox and library module forms cleanly
(3.5 s and 3.3 s); only the prescribed wrapper was used. The dry run
passed server preflight and compilation (commit 5c9810edfb5, nothing pushed).

## Second reading by Q59

Self-audit against the node and complete source definitions, not a claimed
independent agent review: the dispatch brief forbids starting another agent and
assigns the independent reading to the maintainer. Checked that hp and the q-atlas
both use scheme-test surjectivity rather than global point surjectivity alone;
that the final equivalence compares the actual projection to T; and that the
image comes from the base change of the composite, not from p or an arbitrary map.
Checked every conclusion against the mapping above and checked the empty case.
The first docstring formatting pass split hyphenated node ids across lines;
rewrapped it without splitting ids. No mathematical mismatch found.
