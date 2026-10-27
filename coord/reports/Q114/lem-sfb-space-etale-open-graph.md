## Worker report

Item: lem-sfb-space-etale-open-graph. Group Q114, stage 2, 2026-10-24.
Module: `Sheaf.AlgebraicGeometry.SpaceEtaleOpenGraph`.

The node is unchanged mathematically. The module has two real helper definitions and
exactly two postponed theorems, each with proof `sorry` and its portion of the node's
six-step proof in its source/blueprint docstring. Helpers belong to the graph construction
of this node, under the authorized same-notion helper rule; no independent notion or
new definition node is introduced. No proof or data is supplied by a new axiom, arbitrary
map, or undetermined choice.

Source checked: Rydh, author version dated 2010-03-03, Appendix A, Proposition (A.2)
and Corollary (A.3), printed p.35, at
https://davidrydh.se/papers/submersion20100305.pdf . The corollary classifies morphisms
by open graph subspaces with universally injective, surjective projection. The local
Stacks source `literature/stacks-project/spaces-morphisms.tex`,
`lemma-etale-universally-injective-open` (Tag 05W5), and the online tag
https://stacks.math.columbia.edu/tag/05W5 were also read. These support the node's
chartwise and no-quasi-separatedness form. This is a prerequisite node, not a blueprint
unit statement; no source-based correction is needed.

Clause-by-clause rendering:

- The base scheme and size convention are `universe u` and `{S : Scheme.{u}}`.
  All algebraic spaces, scheme tests, and coefficient-free point representatives use
  the existing big-site universe. Point quotients naturally live in `Type (u + 1)`.
- The arbitrary algebraic spaces and their maps to B are `{X Y B : AlgebraicSpace S}`,
  `(f : X ⟶ B)`, and `(g : Y ⟶ B)` in both theorems.
- The sole geometric hypothesis is `(hg : IsChartwiseEtale g)`. It is the exact recorded
  chartwise notion, not `IsEtale g.hom.hom` (which would impose representability).
- The sheaf fibre product is `enlargedFibreProduct f g`, whose data are exactly
  `Limits.pullback f.hom g.hom` and the algebraic-space proof from the recorded
  `fibreProduct_isAlgebraicSpace` theorem. Its projections are those of that sheaf
  pullback; there is no private second product.
- A B-morphism is the subtype `{a : X ⟶ Y // a ≫ g = f}`. The helper
  `etaleGraphSubfunctor f g a` is `Subfunctor.range` of the actual sheaf pullback lift
  of the identity and a. Thus its test sections are precisely `(x,a(x))`.
- An open subspace is the recorded `OpenSubspace (enlargedFibreProduct f g)`;
  equality in the correspondence is equality of `A.val` as a subfunctor, rather
  than equality of chosen open immersion representatives.
- For such A, its first projection is
  `A.val.ι ≫ (Limits.pullback.fst f.hom g.hom).hom`.
  `EtaleGraphPointCondition f g A` quantifies over every `T : AlgebraicSpace S`
  and every `t : T ⟶ X` and requires `Function.Bijective` of `mapPoint` of the
  second projection from the presheaf pullback of that map along `t.hom.hom`.
  Bijective is the conjunction of injectivity and surjectivity. Taking T=X and t=id
  includes original surjectivity; all other t give exactly both required universal
  point conditions. No assumption that point spaces preserve products is used.
- The first conjunct of `space_etale_open_graph` supplies an admissible open subspace
  for every a, with subfunctor equal to its graph. Its second conjunct supplies
  `∃! a` for every admissible A. Together these are precisely the graph bijection;
  openness and equality make the A attached to each a unique as well.
- For every admissible A the same second conjunct supplies
  `e : A.val.toFunctor ≅ X.obj.obj`, with e.hom explicitly equal to the first
  projection. Thus the projection itself is an isomorphism, not an arbitrary
  unrelated identification. Isomorphisms of underlying presheaves are isomorphisms
  of their sheaves/algebraic spaces; here e also shows the open subfunctor is the
  algebraic space X. No extra sheaf structure or atlas choice is assumed for A.
- The last clause of that conjunct is the inverse formula:
  `a.val.hom.hom = e.inv ≫ A.val.ι ≫ (Limits.pullback.snd f.hom g.hom).hom`
  for the uniquely recovered graph morphism. This is pr_Y composed with the inverse
  projection and inclusion; the B-morphism property is retained by a's subtype.
- Arbitrary base change in B is `space_etale_open_graph_baseChange`:
  B1, b, X1, Y1, f1, g1, x and y are arbitrary and hx/hy assert the two cartesian
  squares. Using any cartesian models, rather than only a selected product object,
  expresses exactly the same arbitrary base change. There is no added geometric
  hypothesis on these objects.
- That theorem supplies m from the new product presheaf to the old product, with
  both projection equations. These equations uniquely determine m by the pullback
  universal property, so m is the canonical comparison map, not an arbitrary map.
- For every a the theorem gives the unique a1 over B1 with `a1.val ≫ y = x ≫ a.val`
  and states that its graph is `(etaleGraphSubfunctor f g a).preimage m`.
  This states compatibility of the forward correspondence.
- For every admissible A it supplies an open A1 with `A1.val = A.val.preimage m`
  and the universal point condition over X1. For both uniquely recovered graph
  morphisms it asserts `a1.val ≫ y = x ≫ a.val`. In combination with the main
  theorem's inverse-projection formula, this is compatibility of the inverse
  correspondence as well, including preservation of admissibility.
- There is no quasi-compactness, separation or quasi-separatedness hypothesis, and
  no assumption on X -> B apart from being a morphism. All variables/universes are
  explicit with `set_option autoImplicit false`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  the full subcategory of fppf sheaves with representable diagonal and étale atlas.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, through the bundled product.
  Also read the signatures/docstrings of `etaleCover_pullback` and
  `etale_fibreProduct_isScheme`; these are not additional assumptions.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`:
  `AlgebraicSpace.chartwise_etale_permanence`, imported for the proof plan;
  `IsChartwiseEtale`, `enlargedFibreProduct` and `enlargedFibreProductFst` are the
  existing declarations in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
  reexported by this dependency. Their full definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`, using the
  existing `Point` quotient from `AlgebraicSpacePointClasses`. The point condition
  uses these same point classes, with no second quotient construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, whose
  subtype property is representability of the inclusion by open immersions.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: only its canonical helper
  `AlgebraicSpace.mapPoint`. Added the already-landed `def-sfb-proper-curve-moduli`
  to stmt_deps as authorized by brief-stage2 §5, avoiding a private copy of this
  map. No curve-family definitions or hypotheses are used.
- Proof-only imports: `Sheaf.AlgebraicGeometry.SpaceOpenChartTests` and
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`, matching the stated
  proof dependencies. `lem-sfb-space-etale-monomorphism-open` has no Lean record
  in the read clone, so its eventual proof-only import remains the maintainer's
  task when that node is stated. Nothing in this statement waits for that proof.

Edge cases checked mathematically:

1. X empty: there is one B-map and one admissible graph, the empty subfunctor.
   The universal condition remains vacuous on every empty base-changed source.
2. Y empty with X nonempty: no B-map exists and no open subfunctor has surjective
   projection. The existence/uniqueness clauses do not manufacture one.
3. Y=B and g=id: the only B-map is f; the graph is the full product and projects
   isomorphically. This is not excluded by representability assumptions.
4. The empty graph with nonempty X fails the universal surjectivity conjunct;
   injectivity alone would incorrectly admit it, so both parts are present.
5. A disjoint double étale sheet has a surjective projection but fails injectivity,
   so it is not an admissible graph. Universal conditions are point conditions
   on every algebraic-space pullback, rather than sectionwise injectivity.
6. Nonseparated étale targets (for instance a doubled-origin étale space) and
   non-quasi-compact/non-quasi-separated sources remain legal inputs. Graphs
   are open; no clopen or closed condition was accidentally imposed.
7. Arbitrary, empty, identity and isomorphism base changes are allowed by hx/hy.
   Requiring cartesian squares specifies the base-change objects and imposes no
   additional property on b. The source X is not required to be étale over B.

Searches made before writing (using the prescribed msearch.py wrapper):

- LeanFinder query: "Morphisms to an etale algebraic space correspond bijectively
  to open graph subspaces whose projection is universally bijective on points".
  Eight hits: scheme étale category/forgetful declarations, `IsEtale`, and
  `StandardEtalePresentation.lift_bijective`; none is this algebraic-space result.
- LeanSearch query: "An etale algebraic space has open graphs classifying morphisms".
  Eight hits: scheme/algebra étaleness and the étale locus; no correspondence.
- Loogle first query `IsEtale, IsOpenImmersion` reported unknown unqualified
  identifier. Repeated with `"AlgebraicGeometry.IsEtale",
  "AlgebraicGeometry.IsOpenImmersion"`: successful query, zero hits.
- Mathlib grep query `graph.*[Ee]tale|[Ee]tale.*graph|AlgebraicSpace` in
  AlgebraicGeometry: zero hits through msearch.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for graph/open/étale
  and universal injectivity found scheme graph lemmas, shriek graph comparisons,
  the existing algebraic-space dependencies, and no algebraic-space graph
  classifier. Searching the node id in both source trees gave no existing binding.
  Exact searches for all four new full-name suffixes also gave no matches.

Validation: scompile.py Q114 lem-sfb-space-etale-open-graph compiled the one module
on the server against the live published library, cleanly (sandbox 15.7 s, library
2.4 s); no errors and no unexpected warnings. No local or global build was run.
No statement dispute or node correction.

## Second reading by Q114

I reopened the node and the finished module for a separate self-review; no second
agent was started, as the dispatcher brief prohibits it. The independent maintainer
review remains the project's delivery review.

The seven original statement dependencies are retained. I checked the base objects,
B-map subtype, sole chartwise-étale hypothesis, graph image formula, equality of
subfunctors, both universally quantified point-map properties, projection isomorphism,
and explicit inverse formula against every sentence of the node. All match. In
particular q is not assumed representable, and the point condition does not silently
assume preservation of fibre products by point spaces. The final theorem quantifies
all base-change squares and gives the actual inverse-image subfunctor and the
commuting recovered morphism, so it covers both correspondences, including identity
and empty base changes. The projection equations canonically specify its comparison
map. The graph and admissibility helpers are direct data/predicates, not choices.

The extra landed statement dependency records the previously defined point map;
it adds no mathematical assumption and avoids a duplicate helper. The two postponed
theorems are precisely the node's main correspondence (steps 1–5) and its base-change
clause (step 6), with complete source/proof docstrings. No mismatch was found and no
mathematical statement was changed during the second reading.
