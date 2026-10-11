## Worker report

The module `Sheaf.AlgebraicGeometry.DescendClosedImmersion` states
`AlgebraicGeometry.exists_isClosedImmersion_stage_of_locallyOfFiniteType`, with a
`sorry` proof and no new definitions. No statement correction or dependency module is needed.

Hypothesis and conclusion correspondence:

- The directed set is `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
  The specified index `i₀ : I` ensures nonemptiness without an extra assumption.
- The inverse system of schemes is `D : Iᵒᵖ ⥤ Scheme.{u}`; its functor laws encode
  identity and composition of the transition morphisms.
- Every transition is affine by
  `[∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]`.
- The limit S with its projections is `c : Cone D`, `hc : IsLimit c`.
  Thus S is `c.pt`, and its projection to S₀ is `c.π.app (op i₀)`.
- S₀ is `D.obj (op i₀)` with `CompactSpace` and `QuasiSeparatedSpace` instances,
  expressing precisely quasi-compactness and quasi-separatedness of the scheme.
- X₀ and Y₀ with their structure maps to S₀ are `X₀ Y₀ : Over (D.obj (op i₀))`;
  each underlying scheme has both `CompactSpace` and `QuasiSeparatedSpace` instances.
- The morphism over S₀ is `f₀ : X₀ ⟶ Y₀`. Its over-category condition says that the
  structure maps commute. `[LocallyOfFiniteType f₀.left]` is the finite type hypothesis,
  with no finite presentation hypothesis added.
- The base-changed morphism over S is
  `((Over.pullback (c.π.app (op i₀))).map f₀).left`. The hypothesis `hf` says this
  is a closed immersion.
- The conclusion `∃ (i : I) (h : i₀ ≤ i), ...` supplies the requested later stage.
  Its base-change morphism is
  `((Over.pullback (D.map (homOfLE h).op)).map f₀).left` and is a closed immersion.
  Here `(homOfLE h).op : op i ⟶ op i₀` has exactly the transition direction.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition` in
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`. Its signature and full docstring
  were read. The imported module supplies the inverse-limit API; the theorem here takes
  an arbitrary limiting cone, rather than depending on a particular chosen witness of
  that existence theorem. This is the node's “with limit S” hypothesis.
- `def-weil-pbc-scheme-conventions` is a convention-only record, not a definition.
  Quasi-compactness of a scheme is `CompactSpace`; quasi-separatedness is
  `QuasiSeparatedSpace`, as in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  `CategoryTheory.Over.pullback` in `Mathlib.CategoryTheory.Comma.Over.Pullback`
  constructs exactly these fibre products, and its map is the unique induced
  morphism with first component `pullback.fst ≫ f₀.left` and second component
  `pullback.snd`. Its full definition was read.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.

Edge cases checked: an empty directed set admits no index i₀, as in the node;
preorders need not be antisymmetric; the singleton diagram allows the same stage;
empty X₀ or Y₀ and an empty finite affine cover are allowed (proof step 8 still takes
an upper bound above k); there is no nonempty scheme, field, characteristic, finite
presentation, or Noetherian assumption. The index universe v and scheme universe u
are explicitly bound and independent, so large directed index sets are not excluded.
All binders are explicit; no auto-bound implicit variables are used.

Source checked: [Stacks 01ZP](https://stacks.math.columbia.edu/tag/01ZP) and
[Situation 081D](https://stacks.math.columbia.edu/tag/081D). The local literature
checkout is absent on this machine, so the source pages were opened directly.
They confirm the hypotheses in the node. The theorem docstring follows all eight
DAG proof steps and names their supporting nodes.

Searches (all service calls made through msearch.py and logged in searches.jsonl):

- LeanSearch: “closed immersion descends at a finite stage inverse limit schemes affine
  transition locally finite type”: service unavailable (Internal Server Error);
  no conclusion drawn from this unavailable search.
- LeanFinder: “closed immersion descends to finite stage inverse limit locally of finite
  type morphism schemes”: eight hits, including finite-type morphism detection and
  closed-immersion properties; none states the node.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFiniteType`:
  only `instLocallyOfFiniteTypeOfIsClosedImmersion`, not a descent theorem.
- Mathlib grep: `01ZP|exists_isClosedImmersion|class IsClosedImmersion|class LocallyOfFiniteType`
  in AlgebraicGeometry: the two class declarations, no descent theorem.
- rg of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `exists_isClosedImmersion|overPullbackMap`: the potentially relevant existing theorem
  is `AlgebraicGeometry.Scheme.exists_isClosedImmersion_overPullbackMap`, in
  `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` at line 3356.
  Its full docstring and signature were read: it requires local finite presentation,
  quasi-compactness and quasi-separatedness of the morphism, so it does not state
  this node's locally finite type result. The pullback-snd variant likewise requires
  finite presentation. No exact existing match was found.
- rg of the source repository, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `lem-weil-pbc-descend-closed-immersion|descend_closed_immersion`, and of `lean/Sheaf`
  for `descend.*closed|closed.*descend`: no exact declaration for this node and no
  collision with the chosen declaration name.

Validation: server compile and the delivery dry run are run on the sandbox module.
The second reader supplies the independent reading and delivers; this worker does
not push or write a second-reading section.

## Second reading by F1

I independently opened the delivered node and module, all seven statement dependency
nodes, the recorded limit theorem, and the Mathlib declarations used below. I read
Stacks `limits.tex` directly from the official stacks-project raw source, at
`situation-descent-property` (081D) and
`lemma-descend-closed-immersion-finite-presentation` (01ZP), including its proof.
The local literature checkout is absent. The corresponding source pages are
https://stacks.math.columbia.edu/tag/081D and
https://stacks.math.columbia.edu/tag/01ZP. Despite the source label's name, the
actual assumption is locally of finite type, not finite presentation.

Object, hypothesis, and conclusion list, matched against the Lean:

1. A directed set I: `{I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]`.
   Correct; antisymmetry is not required, in accordance with the directed-set convention.
2. Schemes S_i and compatible inverse transition maps: `D : Iᵒᵖ ⥤ Scheme.{u}`.
   Correct; the functor supplies the identity and composition laws. `Scheme` and its
   morphisms are those of def-pc-scheme (Mathlib's locally ringed space definition).
3. Affine transitions: `[∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]`.
   Correct; I read `IsAffineHom`, whose field is affineness of every affine-open
   preimage, exactly pqf-def-affine-morphism.
4. A specified limit S with projections: `(c : Cone D) (hc : IsLimit c)`.
   Correct; S is `c.pt` and its projections are `c.π.app`. The dependency
   `exists_limit_affine_transition` uses precisely these cone notions. No selected
   existential witness is required: the node already supplies a limit. Its smaller
   index-universe binder imposes no restriction on this theorem, which merely imports
   the module and does not apply that existence theorem in its signature.
5. A specified index 0: `(i₀ : I)`; S_0 is `D.obj (op i₀)`.
   Correct; 0 is a label, not a least element or a numerical index.
6. S_0 quasi-compact and quasi-separated:
   `[CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]`.
   Correct; the convention node defines no additional object. I checked Mathlib's
   quasiSeparatedSpace_iff_forall_affineOpens: the intersections of affine opens are
   compact, agreeing with scheme quasi-separatedness.
7. Schemes X_0 and Y_0 over S_0: `(X₀ Y₀ : Over (D.obj (op i₀)))`.
   Correct; these contain the schemes and their structure morphisms.
8. X_0 and Y_0 quasi-compact and quasi-separated: the four `CompactSpace` and
   `QuasiSeparatedSpace` instances on `X₀.left` and `Y₀.left`.
   Correct; exactly the source's assumptions, with no separatedness imposed.
9. A morphism f_0 over S_0: `(f₀ : X₀ ⟶ Y₀)`.
   Correct; the Over morphism condition asserts compatibility with the structure maps.
10. Its base change f over S: `((Over.pullback (c.π.app (op i₀))).map f₀).left`.
    Correct; I read `Over.pullback`: its objects are the fibre products of each
    structure map with the projection, and its morphism is the pullback lift with
    components `pullback.fst ≫ f₀.left` and `pullback.snd`. I also opened the recorded
    `Limits.pullback`, its projections and lift; this uses def-pc-fibre-product,
    with no private base-change definition.
11. f is a closed immersion: `hf : IsClosedImmersion ...`.
    Correct; I opened the class: closed embedding and surjective stalk maps, exactly
    def-weil-closed-immersion, with no surjectivity of the underlying space required.
12. f_0 locally of finite type: `[LocallyOfFiniteType f₀.left]`.
    Correct; I opened its all-affine-pairs finite-type condition and ring-hom property
    instance, equivalent to def-weil-finite-type-morphism's affine-cover condition.
    The worker report's phrase "finite type hypothesis" here means locally finite
    type; the delivered signature does not add quasi-compactness of the morphism.
13. Conclusion, a stage i at or above 0 and f_i a closed immersion:
    `∃ (i : I) (h : i₀ ≤ i), IsClosedImmersion
    ((Over.pullback (D.map (homOfLE h).op)).map f₀).left`.
    Correct; `(homOfLE h).op : op i ⟶ op i₀`, so this is base change along S_i to
    S_0 in the correct direction. The quantifier is existence of one later stage,
    exactly the node, with neither an all-stages conclusion nor an extra hypothesis.

Edge cases: empty I supplies no i₀ and is excluded by the node itself; a singleton
or a preorder with equivalent indices is allowed. Empty schemes, the zero ring's
spectrum, and an empty affine cover are allowed; proof step 8 explicitly retains
an upper bound above k for the empty cover. No field, characteristic, nonemptiness
of a scheme, Noetherian assumption, finite presentation, or numerical n is present.
`u` and `v` are explicit independent universes, allowing arbitrary index size relative
to the schemes. Every variable is bound. Reversing the order of the two independent
hypotheses hf and locally finite type changes no meaning.

Independent searches, using words different from the worker's:

- LeanFinder via msearch: "a morphism locally of finite type becomes a closed embedding
  after base change to an inverse limit". Eight hits, ordinary closed-immersion
  properties, no matching descent statement.
- Loogle via msearch: `AlgebraicGeometry.IsClosedImmersion,
  CategoryTheory.Limits.IsLimit`. Zero hits.
- LeanSearch via msearch: "closed immersion of a base changed locally finite type
  morphism descends along affine transition inverse limit". Service unavailable
  (Internal Server Error), recorded in searches.jsonl; no absence verdict from it.
- Independent rg on Mathlib AlgebraicGeometry, WeilConjectures, and lean/Sheaf:
  `closed.*(stage|limit)|[Dd]escend.*[Cc]losed|isClosedImmersion.*(stage|limit)`.
  I opened the upstream declarations `Scheme.exists_isClosedImmersion_pullback_snd`
  and `Scheme.exists_isClosedImmersion_overPullbackMap`: both add local finite
  presentation (plus morphism quasi-compactness and quasi-separatedness), so neither
  is an exact existing match. I also opened
  `Scheme.exists_isClosedImmersion_comp_π_of_isAffine`: it concludes a composite
  from a fixed scheme into a stage is closed, not the base-changed f_i in this node.
  The module's declaration name and source label were searched in lean/Sheaf,
  WeilConjectures, and dag/lean_names_upstream.json; no collision or exact match.

No new nodes, dependency modules, or statement_change are in this delivery.
No mismatch in the Lean statement or node was found; both are retained verbatim.
The eight docstring proof steps follow all eight node steps, with their dependency
names and source place. The module has only one theorem with a sorry proof and
no definitions or additional proved assertions. Imports supply the inverse-limit
scheme API and the over-category pullback used in the signature. Lines are at most
100 characters, and the declaration is in AlgebraicGeometry, without a Sheaf prefix.
Only this independent reading and its validation record were appended to the report.

Validation: scompile.py compiled the delivered module on the server in 1.6 s,
exit code 0, with no errors or warnings.

## Reviewer fix (R-dci1134)

The index type was `{I : Type v}` with `v` independent of the scheme universe `u`.
Per the recorded limit form (M1 d2371fc68, C1 02bc80ff3, G1 117cfd333) the index
must live in the schemes' universe: changed to `{I : Type u}` and dropped
`universe v`. The two second-reading claims that the independent universe "imposes
no restriction" and "allows arbitrary index size" were the miss. No other change.
