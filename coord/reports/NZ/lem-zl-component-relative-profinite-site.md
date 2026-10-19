## Worker report

The delivery states `AlgebraicGeometry.ProEtale.component_relative_profinite_site` in
`Sheaf.Paper.ComponentRelativeProfiniteSite`. The original natural-language statement,
proof, and dependency lists are unchanged. There is one postponed theorem, with the
node's twelve-step proof in its docstring. Five fully defined helpers package parts of
this same construction; no independent notion or new DAG node is introduced.

Source checked: Hemo–Richarz–Scholbach, *Constructible sheaves on schemes*, arXiv
2305.18131v1, paragraph immediately preceding (4.1) and its factorization sentence
(https://arxiv.org/html/2305.18131v1#S4.SS1); Bhatt–Scholze, *The pro-étale topology for
schemes*, Lemma 2.2.8, its more precise statement, and proof, printed page 9
(https://arxiv.org/pdf/1309.1198). The local literature checkout contains the citation
list but not the PDFs, so these source texts were read online. In particular, BS's
right-adjoint description justifies the universal mapping property used to specify the
canonical functor, and HRS specifies the finite-clopen presentation and factorization.

Hypotheses and clauses, in the order of the node:

- An affine scheme T: `(T : Scheme.{u}) [IsAffine T]`, with no nonempty, connected,
  reduced, Noetherian, separated, or weak-contractibility hypothesis.
- S is the connected-component quotient with the quotient topology:
  `affineComponentSpace T` is literally `Profinite.of (ConnectedComponents T)`.
  The compact, Hausdorff, and totally disconnected proofs come from the recorded
  `spectralSpace_connectedComponents_profinite`. Spectrality is assembled from
  Mathlib's scheme T0, quasi-sober, prespectral, affine compactness and affine
  quasi-separatedness instances. No space is chosen by an existence theorem.
- The smaller/larger universe convention: schemes and profinite carriers have
  universe u; small presentation indices are `I : Type u` with `SmallCategory I`;
  set sheaves take values in `Type (u + 1)`. The pro-étale category retains its
  object universe u+1 and morphism universe u. No equality of those universes is
  imposed. No additional `EssentiallySmall` assumption is introduced.
- The small scheme site is exactly `T.ProEt` and `Scheme.ProEt.topology T`, i.e.
  Mathlib's category of weakly étale T-schemes and its fpqc/pro-étale topology.
  Thus a functor value already has a weakly étale structure map.
- The relative profinite site is `Over (affineComponentSpace T)` with
  `(coherentTopology Profinite.{u}).over (affineComponentSpace T)`. This is the
  localized finite jointly surjective topology; it is not an étale scheme site.
- A map E -> S is an `E : Over (affineComponentSpace T)`, with actual continuous
  structure map `E.hom`. `componentFiniteStage A C q f` is the categorical pullback
  of the finite-set map f along q, using its projection to S. The `Function.Surjective q`
  condition in `IsComponentFiniteStage` makes q a finite clopen quotient; finite
  discrete targets make all its fibres clopen. An isomorphic presentation is allowed.
- Existence of the stipulated cofiltered presentation: for every E the theorem
  supplies I, its small category and cofiltered structure, a diagram D and cone c,
  with `c.pt = E`, `Nonempty (IsLimit c)`, and `IsComponentFiniteStage (D.obj i)`
  for every i. Cofiltered includes a nonempty index category; no restriction is put
  on E or on its structure map being surjective.
- The finite scheme stage with restricted structure sheaves:
  `componentFiniteOpen T A C q f a` is the open subset
  `{t | q (ConnectedComponents.mk t) = f a}`. Its complement is also open because
  the target is finite discrete. `componentFiniteScheme` is the coproduct in
  `Over T` of `Over.mk (componentFiniteOpen ... a).ι`. Mathlib's `Scheme.Opens.ι`
  uses the actual restriction of the structure sheaf. The theorem supplies an
  isomorphism in `Over T` between this object and the value at the finite stage.
- The affine weakly étale inverse limit: the functor F takes values in T.ProEt,
  all `(F.obj E).left` are affine, and for EVERY cofiltered presentation D of the
  required type and EVERY limiting cone c, the image cone under
  `F ⋙ Scheme.ProEt.forget T` is limiting in `Over T`. This is the inverse limit
  in T-schemes, rather than only a limit of underlying spaces or only one chosen
  presentation. Every transition is affine because its source and target are
  affine schemes (Mathlib `isAffineHom_of_isAffine`); this is implied by the
  explicit affineness clause and does not need an extra hypothesis.
- Canonical construction and functoriality: the existential F is a genuine functor,
  so it includes identity/composition equations. It is not an arbitrary map or
  merely a bare nonempty functor type. A family of continuous projections p is
  over S and natural in E. For every T-scheme W and continuous g:W -> E over S,
  the theorem requires a UNIQUE T-morphism m:W -> F(E) with p m = g. This is the
  universal property of the component pullback ringed space in BS 2.2.8 (continuous
  maps to E factor through the connected-component quotient). It characterizes
  the functor's objects and arrows up to unique projection-compatible isomorphism.
  Together with the IsLimit assertion for every presentation, it expresses canonical
  presentation independence, including comparisons with any other limiting cone.
  This is an equivalent specification of the source's construction, not an added
  assumption and not a substitution of an unspecified structure map.
- Preservation of finite limits: `PreservesFiniteLimits F`, in the actual sites.
- Preservation of finite coproducts, including the empty one:
  `∀ (A : Type u) [Finite A], PreservesColimitsOfShape (Discrete A) F`.
- Covering families: for every finite A and jointly surjective family f over any
  E₀, its image `Presieve.ofArrows ...` belongs to `Scheme.ProEt.precoverage T
  (F.obj E₀)`. This is the actual pro-étale precoverage, not just surjectivity on
  points or a weakened topology.
- Induced geometric morphism π: a `CategoryTheory.GeometricMorphism` from set
  sheaves on T.ProEt to set sheaves on the relative profinite site. The displayed
  natural isomorphism after `sheafToPresheaf` identifies its DIRECT IMAGE with
  precomposition by F.op, simultaneously on objects, arrows, and restrictions.
  This pins down the site-induced morphism; the adjunction and left exactness
  are fields of the recorded `GeometricMorphism` structure.
- Slice projection q: a `GeometricMorphism` from relative profinite sheaves to
  absolute profinite sheaves with inverse image equal to
  `(coherentTopology Profinite).overPullback (Type (u+1)) S`. This is the actual
  slice restriction functor. Its right adjoint is consequently the slice projection,
  uniquely up to adjunction-compatible isomorphism.
- Final factorization: `Nonempty (profinitePointSetSchemeInverseImage T ≅
  (π.comp q).inverse)`. The left side is exactly the recorded condensed-point
  inverse image at T; `GeometricMorphism.comp` puts inverse images in the order
  q.inverse followed by π.inverse. By the recorded mate convention this is the
  claimed isomorphism p_T ≅ q_S π_T of geometric morphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite` (the exact recorded declaration).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `.topology`,
  `.precoverage`, and `.forget` (the repaired recorded small-site interface).
- `def-weil-size-convention`: a metatheoretic convention; its record correctly has
  no object declaration. Rendered by the explicit universes above.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `CategoryTheory.GeometricMorphism`
  and `.comp`; the mate convention is used for the interpretation of the final iso.
- `Sheaf.Paper.ProfinitePointPullback`: `profinitePointSetSchemeInverseImage`,
  `profinite_point_pullback`, and `profinite_point_pullback_set_coherence`. The first
  is the actual constant-point inverse image used in the signature. Its definition
  composes `profinitePointSetInverseImage` with `Scheme.proEtaleSheafInverseImage`
  along `toSpecZ T`, without changing the coefficient universe.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme` and `.ι`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, `.overPullback`.
- `Mathlib.Topology.Category.Profinite.Basic` and `.Limits`: actual profinite spaces,
  the functor `FintypeCat.toProfinite`, and pullbacks.

Recorded proof modules are imported without `public`: `Sheaf.Topology.FiniteQuotientFiberProduct`
(`Topology.finite_quotient_fiber_product`), `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`
(`CategoryTheory.slice_subtopos_site_presentation`), `Sheaf.RingTheory.IndEtaleStability`
(`RingHom.indEtale_principalZariski_stability`), and `Sheaf.Paper.ProfiniteTestObjectFunctor`
(`profinite_test_object_functor`). The scheme-affineness proof dependency is imported from
Mathlib.AlgebraicGeometry.Morphisms.Affine. Other proof dependencies are already public
statement imports or reachable through them. The proof-only node
`lem-zl-affine-component-site-projection` has no recorded Lean declaration/module;
there is consequently no module to import for it. This stage does not prove the theorem
or require that unstated proof input to type its signature, and no private replacement
for that node is introduced.

Edge cases checked before writing and again against the final signature:

- T empty: S is empty; only empty profinite objects map to S. No inhabitance assumption
  is present. The finite quotient C and its source A can both be empty.
- E empty with nonempty S: allow A empty; F(E) is the empty scheme by the finite stage
  and universal property. Cofiltered indices remain nonempty, as they should.
- E = S with its identity: the universal property gives F(E) canonically T; p is the
  component quotient. The terminal finite stage uses singleton finite sets.
- Repeated finite blocks: f need not be injective. The coproduct indexes A, so two
  elements over the same block give two distinct copies of its restricted subscheme.
- A finite quotient q is required surjective, but E.hom is not. Closed embeddings,
  nonsurjective profinite maps and point fibres are covered.
- Empty finite coproducts and empty jointly surjective families over the empty object
  are included by `[Finite A]` without `[Nonempty A]`.
- The universal mapping property allows arbitrary W over T. Its elementary extension
  from affine W is exactly the affine-cover gluing in proof step 6; it introduces no
  extra assumption on the node's T or E.

Searches for existing statements/definitions (2026-10-18):

1. `msearch.py ... leanfinder` query: “An affine scheme has a relative profinite
   component pullback functor preserving finite limits and inducing a geometric
   morphism to sheaves on profinite spaces over its connected components”. Eight
   hits were affine-transition/global-section limit facts and affine approximation;
   none states this relative site construction or factorization.
2. `msearch.py ... loogle 'Profinite, LocallyConstant'`: nine hits, including
   `Profinite.exists_locallyConstant` and its finite-target variants, and condensed
   locally-constant colimit facts. No relative component-site theorem.
3. `msearch.py ... grep 'LocallyConstant.*(Spec|RingHom)|[Cc]omponent.*[Pp]ullback|[Rr]elative[Pp]rofinite'`:
   thirteen Mathlib hits, chiefly generic categorical pullback components and
   `LocallyConstant.comapRingHom`/`mapRingHom`; no matching construction.
4. `msearch.py ... leansearch` query: “For an affine scheme the profinite component
   pullback preserves finite limits and covering families and gives a geometric
   morphism factoring the condensed point morphism”. Eight hits on affine scheme
   pullbacks, affine limits and unrelated condensed finite limits; no match.
5. `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` for
   the item id, component-site and relative-profinite names: no exact statement.
   Upstream `WeilConjectures.RingTheory.ProEtale.WContractible` contains the real
   ring `WContractification.PullbackProfinite` construction and its topological
   pullback, which was read; it does not supply the functor, presentation theorem,
   coverings, geometric morphism and factorization of this node. We do not define
   a second copy of that ring.
6. `rg` over Mathlib, upstream sources, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for all six proposed full-name suffixes found no collisions. DAG searches found
   the related proof node `lem-zl-affine-component-site-projection`, which has a
   different, stronger evaluation-formula statement and no Lean interface; it is not
   being duplicated here. Existing point tests concern absolute profinite K, rather
   than arbitrary profinite maps E -> pi0(T), so they are reused for p_T instead.

Validation: `scompile.py NZ lem-zl-component-relative-profinite-site` compiled the file
both as a sandbox module (4.1 seconds) and under its delivered library path (3.1 seconds),
within the 60-second per-file limit. No errors or warnings. `autoImplicit false` is set;
all universes and binders are explicit. No global build was run. The only `sorry` is
the entire proof of the named theorem matched by this node. All helpers have real data.
No statement dispute or source correction is needed.

## Second reading by NZ

The dispatcher brief assigns the independent delivery review to the maintainer and
forbids starting other agents. This section records the worker's second pass, not a
claim that a separate reader was launched.

I reopened the node and final module and matched every clause as listed above.
In particular I checked the pullback projection is the projection to S, not the
finite-set factor; each open is the inverse image of the label f(a), not the image of
that label; its scheme uses the restricted structure sheaf; and the coproduct is over
A so repeated labels remain repeated copies. The presentation clause quantifies over
all permitted diagrams and limit cones, rather than a chosen tower. The mapping
property is over T with its continuous projection over S, so its uniqueness really
identifies the canonical component pullback. The cover conclusion uses the pro-étale
precoverage itself. The direct-image natural isomorphism has target precomposition
by F.op, whereas the slice functor is fixed on inverse images. Finally `(π.comp q).inverse`
is q.inverse followed by π.inverse, with the absolute point inverse image on the other
side of the iso. Neither a universe-equality assumption nor a nonempty condition was
introduced. No mathematical mismatch was found; compilation required explicitly
assembling the affine scheme's SpectralSpace instance and qualifying
`Functor.whiskeringLeft`. All these changes are in the final compiled file.
