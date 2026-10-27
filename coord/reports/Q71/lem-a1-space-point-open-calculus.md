## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.point_open_calculus` in
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`. It is one theorem containing
all clauses of the node, with one `sorry`. No mathematical proof or definition is added.
The node's natural-language statement and accepted proof are unchanged.

Hypotheses and clauses, in the order of the node:

- The scheme base is `{S : Scheme.{u}}`; all spaces are `AlgebraicSpace S`. The same
  universe `u` governs the big site, test schemes, and field representatives. Points
  live in `Type (u + 1)` through the existing `Point` definition. No nonemptiness,
  separation, representability, quasi-compactness, or size hypothesis is imposed on
  the arbitrary morphisms.
- For arbitrary `a : A ⟶ B` and `c : C ⟶ B`, the first conjunct quantifies over
  `x : Point A.obj.obj` and `z : Point C.obj.obj` whose images under `mapPoint` agree.
  It supplies `t : Point (Limits.pullback a.hom c.hom).obj` mapping to both. This is
  precisely surjectivity of the canonical comparison to the set-theoretic fibre
  product, expressed by its compatible-pair lifting property. The pullback used is
  the sheaf pullback of the recorded fibre-product dependency, with its actual
  projection maps; no arbitrary replacement or extra representability hypothesis
  is present.
- The second half of that conjunct is
  `pointImage (Limits.pullback.snd a.hom c.hom).hom =
  mapPoint c.hom.hom ⁻¹' pointImage a.hom.hom`. It states the projection-image formula,
  using the recorded image on field representatives.
- The second conjunct assumes `IsRepresentable a.hom.hom` and says
  `IsSurjective a.hom.hom ↔ Function.Surjective (mapPoint a.hom.hom)`.
  `IsSurjective` is the existing scheme-test definition, so this is exactly
  surjectivity on every scheme base change if and only if surjectivity on points.
- The third conjunct is `Continuous (mapPoint a.hom.hom)` for every space morphism,
  with the existing `pointTopologicalSpace` instances on source and target.
- The fourth conjunct assumes `IsEtale a.hom.hom` and concludes
  `IsOpenMap (mapPoint a.hom.hom)`. This predicate already includes representability.
- For every `J : OpenSubspace B`, the fifth conjunct begins with
  `Topology.IsOpenEmbedding (mapPoint J.val.ι)`. An open embedding is injective,
  induces exactly the subspace topology, and has open range. This states exactly
  the asserted homeomorphic identification with an open subset, without choosing
  a homeomorphism or duplicating the point space.
- For any scheme atlas, `U : Over S` and `p : yoneda.obj U ⟶ B.obj.obj` with
  `IsEtale p` and `IsSurjective p`, that same conjunct supplies `V : Over S`,
  `i : V ⟶ U`, and `q : yoneda.obj V ⟶ J.val.toFunctor`. The condition
  `IsPullback q (yoneda.map i) J.val.ι p` makes V the actual scheme representing
  `U ×_B J`; `IsOpenImmersion i.left` makes its image an underlying open of U;
  `schemePointMap p ⁻¹' pointImage J.val.ι = Set.range i.left` is the precise
  atlas inverse-image identification. There is no unintroduced or freely chosen
  projection: the representing square ties both maps to p and the inclusion.
- The sixth conjunct is
  `pointImage J₁.val.ι ⊆ pointImage J₂.val.ι ↔ J₁.val ≤ J₂.val`.
  The right side is the existing pointwise order on subfunctors, equivalently
  the inherited order on open subspaces.
- The last conjunct says that `pointImage J.val.ι = Set.univ` implies
  `J.val = ⊤`. The top subfunctor is the entire presheaf of B, so this says
  precisely that an open subspace with full point image equals B.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, and `IsSurjective`.
  The representability definition uses `IsPullback` of actual presheaf maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  its common-field relation, `Point`, and `schemePointMap`, imported publicly
  through the recorded topology module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `PointRepresentative.map`,
  `pointImage`, and `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, its
  underlying subfunctor `.val`, inclusion `.ι`, and inherited partial order.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, including its sheaf-pullback formulation.
  The theorem uses those sheaf pullbacks and their presheaf projection maps.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: the existing canonical `mapPoint`
  only. This helper is recorded by the landed node `def-sfb-proper-curve-moduli`;
  that node is added to `stmt_deps` under the explicit permission to add landed
  dependencies. Its point-map definition applies `PointRepresentative.map` by
  `Quot.map`; no moduli, properness, or curve condition enters this statement.
- Proof imports include `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`
  (`exists_affine_etale_cover_and_point_topology`),
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (open-immersion instance,
  `Etale.etale_comp`, `Etale.of_comp`), and
  `Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.SpecToEquivOfField`,
  `descResidueField_stalkClosedPointTo_fromSpecResidueField`,
  `fromSpecResidueField_apply`). `IsOpenImmersion` from the recorded
  `Mathlib.AlgebraicGeometry.OpenImmersion` is publicly available through the
  open-subspace module. Thus all already stated proof dependencies are imported,
  directly or through the corresponding statement dependencies.

The source read was `literature/stacks-project/spaces-properties.tex`, the
statements and proofs of lemma-points-cartesian (03H4),
lemma-characterize-surjective (03H5), lemma-topology-points (03BX),
lemma-open-subspaces (03BZ), and lemma-etale-open (03IR). The natural-language
proof in the declaration follows all seven accepted node proof steps, naming
its dependencies and explaining the passage from scheme points to point classes,
common-field lifting, scheme tests, the final topology, atlas reduction of openness,
and the scheme-test proof of subfunctor containment. The representable-source
extension of 03H5 is exactly the node's scheme-test argument.

Edge cases checked before writing:

- Empty source, empty pullback, and empty open subspace: the compatible-pair
  condition and image formula have the expected empty sets. An empty-domain
  point map is an open embedding; a full-image empty open forces the ambient
  point space to be empty and the scheme-test argument still gives the full
  subfunctor. Empty scheme atlases of empty spaces are allowed.
- A zero/empty base scheme and identity morphisms/identity scheme atlases are
  allowed. No `Nonempty` or nontriviality binder was introduced.
- Arbitrary nonrepresentable a and c remain allowed in the first and third
  conjuncts. Representability appears only in its stated surjectivity criterion,
  and is already part of representable étaleness and open-subspace definitions.
- Fibre-product point comparison need not be injective, so the first clause
  asserts only compatible-pair surjectivity. A general continuous point map need
  not be open or injective: these conclusions occur only in their stated cases.
- Inclusion of point images reflects inclusion only for open subfunctors; the
  theorem does not extend this assertion to arbitrary subfunctors or closed
  immersions. Equal and nested open subspaces, and the top subfunctor, are covered.
- The atlas pullback condition specifies the representing square, so it cannot
  be satisfied by an unrelated open scheme or map with the same domain.

Searches for existing declarations:

- `msearch.py ... leanfinder "Point images of fiber products of algebraic spaces,
  continuous point maps and open subspaces"`: eight scheme-only results, including
  `Scheme.Pullback.Triplet.exists_preimage`,
  `Scheme.Pullback.exists_preimage_pullback`, and
  `Scheme.exists_preimage_of_isPullback`. None states the algebraic-space result.
- `msearch.py ... loogle
  "AlgebraicGeometry.Scheme.Pullback.forget_comparison_surjective"`: zero hits;
  the service reported the identifier unknown. This is not used as a declaration.
- `msearch.py ... grep "point.*pullback|mapPoint|OpenSubspace" AlgebraicGeometry`:
  five hits in Mathlib's scheme `PullbackCarrier`, none for these algebraic spaces.
- `msearch.py ... leansearch "Every morphism of algebraic spaces is continuous on
  point classes and an open subspace gives an open embedding"`: eight results,
  concerning schemes, presheafed spaces, and generic open embeddings. These provide
  the general topological meaning of `IsOpenEmbedding`, not this theorem.
- `rg` of `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` for point maps,
  `schemePointMap`, and `OpenSubspace`, and a follow-up search across
  `lean/Sheaf/AlgebraicGeometry`, found the existing `mapPoint` in
  `ProperCurveModuli.lean`. Its full definition and owning DAG record were read
  and reused. Existing `openSubspace_points_orderIso` in
  `AlgebraicSpaceEtaleOpenImage.lean` states only one part of the present calculus
  and is downstream; it is not used to prove its own prerequisite.
- `rg` across `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-a1-space-point-open-calculus` found only references in later proof docstrings,
  not a declaration stating it. Concept searches for point maps, pullbacks, and
  open-subspace images upstream found scheme facts, not the present statement.
- An exact-name search for `point_open_calculus` in Mathlib, `WeilConjectures`,
  and `Sheaf` found no existing declaration.

No node fault, statement correction, missing notion, new definition node, or
unusable dependency interface was found. No statement is disputed.

Validation: the prescribed `scompile.py Q71 lem-a1-space-point-open-calculus`
compiled this file in sandbox and library modes on the server, cleanly (7.1 s
and 4.6 s respectively). All universes and variables are explicitly bound and
`set_option autoImplicit false` is set. All Lean lines have at most 100 characters.

## Second reading by Q71

The same dispatcher worker re-opened the node and the compiled file and checked
all seven conjuncts against the statement. This is a self-check, not a claimed
independent worker review; the task explicitly prohibits starting other agents
and assigns the independent review to the maintainer after delivery.

The first conjunct was checked for arbitrary a and c and the correct second
projection, the second for representability and both directions of surjectivity,
the third and fourth for the distinct continuity and étale-openness hypotheses,
and the fifth for an open embedding plus every scheme atlas and a genuine open
representing square. The sixth uses the actual subfunctor order, and the seventh
uses equality with the full subfunctor, rather than an arbitrary isomorphism.
`IsOpenEmbedding` accounts jointly for injectivity, the open image, and the stated
homeomorphic identification. The compatible-pair formulation is precisely onto
the point fibre product, without imposing the false claim of injectivity.

The only addition to the node is its Lean record and the landed dependency for
`mapPoint`; no mathematical clause or accepted proof step changes. The review
found no mismatch requiring a change to the compiled statement.
