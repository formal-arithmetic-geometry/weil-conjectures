## Worker report

Stage 2, NY, 2026-10-17. The delivery states
`SSet.Enhanced.quillenB_discreteFibration_baseChange` in
`Sheaf.CategoryTheory.QuillenBDiscreteFibrationBaseChange`. Its proof is the only `sorry`.
The module constructs the specialized nerve diagram, its actual constant-path comparison,
and its three path-pullback projections. The definition module is
`Sheaf.CategoryTheory.DiscreteFibration`. Nothing is proved at this stage.

The item's original statement, proof, proof dependencies, and source are unchanged.
Its statement dependencies gain only the new definition `def-coef-discrete-fibration`.

Clause-by-clause translation:

- Small ordinary categories: `E D B : Cat.{u, u}` and functors `U : E ⟶ B`,
  `V : D ⟶ B`. Bundling uses precisely Mathlib's ordinary small categories and functors.
  `u` is arbitrary and explicitly bound. As in the node, take a universe containing all
  categories, their comma categories and the realization/singular constructions.
- The comma `(U ↓ b)` is Mathlib's `CostructuredArrow U.toFunctor b`. Its objects have
  `.left : E` and `.hom : U.obj left ⟶ b`; a morphism has `.left : e ⟶ e'` and
  `CostructuredArrow.w : U.map h ≫ α' = α`. These are exactly the indicated objects
  and arrows, with no reversal of the comma direction.
- Postcomposition by every arrow is `CostructuredArrow.map (S := U.toFunctor) β`.
  The binder `hU` quantifies over both objects and every such arrow and says that
  its `nerveMap` is `IsWeakHomotopyEquivalence`.
- Discrete fibration: `hV : V.toFunctor.IsDiscreteFibration`. The new definition
  quantifies over every target `d`, base source `b` and `β : b ⟶ V.obj d`.
  `∃! l : Σ d' : D, d' ⟶ d` requires uniqueness of the pair, including its domain.
  `∃ h : V.obj l.1 = b, eqToHom h.symm ≫ V.map l.2 = β` is exactly equality
  of the image arrow after transporting its source. Equality witnesses are propositions
  and cannot add extra lifts. This is strict uniqueness, not uniqueness up to isomorphism.
- Strict pullback category: `pullback U V` in Mathlib's `Cat`, using
  `Mathlib.CategoryTheory.Category.Cat.Limit`. This is an ordinary categorical limit,
  not an iso-comma/bicategorical pullback. The limit construction uses compatible
  object families and compatible arrow families; for this cospan these are the pairs
  with equality of images in the node. Its two projections are `pullback.fst U V`
  and `pullback.snd U V`; `pullback.condition` is strict equality of functors.
- Nerves: `quillenBNerveFunctor` is literally
  `CategoryTheory.nerveFunctor ⋙ SSet.toTop ⋙ TopCat.toSSet`. Hence the four objects
  and arrows in the conclusion are the indicated nerve square after the functorial
  Kan replacement `R = Sing|-|` from proof step 3. No independent replacement map,
  arbitrary equivalence, or additional Kan hypothesis is passed as input.
- Path-space model: `quillenBPathPullback U V` is the actual iterated Mathlib pullback
  with `evaluation Δ[1] _ (stdSimplex.obj₀Equiv.symm 0)` followed by endpoint 1.
  It is `RN(E) ×_{RN(B),ev₀} Fun(Δ¹,RN(B)) ×_{ev₁,RN(B)} RN(D)`.
  All pullbacks and the internal hom are the existing degreewise simplicial constructions.
- Canonical comparison: `quillenBBaseChangeComparison U V` is constructed by two
  `pullback.lift`s. Its object coordinates are the replaced nerve maps of the two
  projections, and its interval coordinate is their first composite with `RN(U)`
  followed by `constantDiagrams Δ[1] _`. The proof obligations use endpoint normalization
  of constant diagrams and `pullback.condition`; no data is postponed.
- Homotopy-pullback assertion: the first conjunct is exactly
  `IsWeakHomotopyEquivalence (quillenBBaseChangeComparison U V)`, using the recorded
  realization/path-component/all-based-homotopy-group definition. This is the node's
  definition of a homotopy-pullback square after Kan replacement.
- Naturality: the second conjunct quantifies over every second diagram satisfying the
  same two hypotheses and every strictly commuting triple `(a,b,c)` with equations
  `hu`, `hv`. Its `t` has all three coordinates prescribed by `quillenBPathFst`,
  `quillenBPathSnd`, and `quillenBPathEdge`; the last equation postcomposes the entire
  path by `RN(c)`. These projections jointly determine `t` uniquely by the universal
  property of the two pullbacks. The final equation compares the actual comparison
  maps using `RN(pullback.map ... a b c hu hv)`. Thus this asserts naturality of the
  specified comparison, retaining higher simplices, not merely existence of abstract
  equivalences of source and target.
- No ordinary-category model structure, localization, fibrant-category axioms,
  nonemptiness, or invertibility hypotheses appear.

Dependencies used:

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`,
  `evaluation`, `constantDiagrams`, and the Mathlib `nerve`, `nerveMap`, `SSet`, internal
  hom, realization and singular constructions it publicly imports. Read its full recorded
  statement and the source definitions of the weak-equivalence and endpoint conventions.
- New `def-coef-discrete-fibration`, module `Sheaf.CategoryTheory.DiscreteFibration`:
  `CategoryTheory.Functor.IsDiscreteFibration`.
- Mathlib `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`:
  `CostructuredArrow`, `CostructuredArrow.map`, and `CostructuredArrow.w`;
  `Mathlib.CategoryTheory.Category.Cat.Limit`: the ordinary `Cat` limit instance.
- The already stated proof nodes are imported non-publicly: RealizationFiniteLimits,
  PathFibrationReplacement, RightFibrationSpaceFiber,
  SimplicialHomotopyEquivalenceWeak, KanRealizationSerre,
  SerreHomotopyExactSequence, SpacesHomotopyFiberDetection (all under their recorded
  `Sheaf.AlgebraicTopology` or `Sheaf.CategoryTheory` modules).
- `lem-cbc-realization-singular-unit-weak` and
  `lem-coef-quillen-b-comma-homotopy-fiber` have no Lean record in the read snapshot.
  They are proof-only prerequisites; their proof roles remain in the full seven-step
  docstring, and there is no missing object needed to elaborate this statement.

Acyclic construction choice: the existing generic path-model helpers
`SSet.Enhanced.homotopyPullbackComparison`, `IsHomotopyPullbackSquare`,
`simplicialHomotopyPullback`, and `simplicialHomotopyPullbackMap` were read in
RelativeInfinityCone, SourceAttachmentGluing, and KanHomotopyPullbackInvariance.
Each owning node has this item in its complete dependency closure (144, 143 and
138 nodes respectively in the read snapshot). Importing these modules here would
make a cycle. This delivery introduces no second generic homotopy-pullback notion:
its helpers are the particular replaced nerve cospan and comparison of this item,
constructed directly by the existing Mathlib pullbacks and the recorded constant/endpoint
maps. All ten original proof dependencies have acyclic closures avoiding this item.

Edge cases checked mathematically before writing:

- Empty D: the strict pullback has no objects and the path model has an empty last
  coordinate, so the comparison is the empty-to-empty map. The unique-lift condition
  on an empty domain is correctly vacuous and does not assert nonemptiness.
- Empty B: both E and D must be empty. No inhabitance is hidden in any construction.
- Empty E with nonempty D: the first coordinate of the path model is empty. All comma
  transition nerves are empty-to-empty maps, giving exactly the expected case.
- Identity V: the unique lift has the prescribed source and the comparison is the
  mapping-path replacement comparison. Identity U has contractible overcategories.
- A discrete category mapping to a point is a discrete fibration; a one-object category
  with a nontrivial automorphism mapping to a point is not: the pair-uniqueness clause
  detects its distinct arrows. A codiscrete category with two isomorphic objects over
  a point is also rejected, because its lift domains differ. Thus the predicate is
  not the weaker general Cartesian-fibration condition.
- For a point mapping to BG, the comma category is discrete on G and every transition
  acts by a permutation, so the comma hypothesis holds and gives the expected loop
  space fibers. In general the hypothesis is tested on the actual comma nerves.
- Naturality includes identity maps and arbitrary commuting triples. Its path-coordinate
  equation prevents an arbitrary choice of map between the two path pullbacks.

Searches (actual calls are also retained verbatim in sandbox `searches.jsonl`):

- `msearch.py ... leansearch` and `... leanfinder`, query
  `Quillen theorem B base change along a discrete fibration is a homotopy pullback of nerves`:
  eight hits each, including ordinary nerve adjunctions, Cech nerves, and general model
  category fibration base-change declarations. None is this theorem.
- `msearch.py ... loogle '"DiscreteFibration"'`: zero hits.
- `msearch.py ... grep '[Dd]iscrete[Ff]ibration|Quillen.*[Tt]heorem|[Hh]omotopy[Pp]ullback'`:
  zero hits. The earlier CategoryTheory grep returned ordinary Cat/ComposableArrows
  constructions, not weak homotopy pullback statements.
- Direct `rg` in upstream `WeilConjectures` for this blueprint id and
  `DiscreteFibration|discrete.fibration|Quillen.*[Bb]`: no matches.
- Direct `rg` in side `lean/Sheaf` located the generic path-model modules above;
  their full source signatures and definitions were read and their dependency closures
  checked. They do not state the item and cannot be imported acyclically.
- Direct name search in Mathlib, upstream, side Lean, and `dag/lean_names_upstream.json`
  found none of this delivery's declaration names.
- For the new definition: `leansearch 'discrete fibration functor unique lift every arrow
  into the image of an object'` and `leanfinder 'a discrete fibration of ordinary categories
  has unique lifts with a specified target'` return general `IsFibered`, `IsPreFibered`,
  Cartesian-lift and `HasFibers` declarations, which do not impose strict unique lifts.
  Loogle and Mathlib CategoryTheory grep return zero matches. DAG grep finds only the
  four consumer statements listed in the new node's search record, no definition node;
  `tools/blueprint_refs.py search 'discrete fibration'` returns zero blueprint matches.

Source read: Cisinski's online PDF, Lemma 4.6.9, Proposition 4.6.11 and Corollary 4.6.12,
printed pp. 179–183. Proposition 4.6.11(iii) gives the homotopy-Cartesian conclusion for
left fibrations; dualizing gives the overcategory/right-fibration convention of this item.
The statement's explicit unique-lift condition specializes the latter to ordinary discrete
fibrations. No source-based statement correction is needed; no disputed statement found.

Validation: both delivered modules compiled separately in dependency order through
`scompile.py`, in sandbox and library positions. No errors and no warnings. The only
postponed theorem is the item and it has its matching node and complete proof docstring.
The prescribed delivery dry run is run after final report/record preparation and must
print OK before the worker returns READY.

## New nodes

`def-coef-discrete-fibration`, in the item's `sec-six-functors` chapter and unit, defines
exactly the unique lift of every base arrow into an image object, with the source object
included in uniqueness. Source: the ordinary-category specialization in the item's
statement, using Cisinski Proposition 4.6.11 dual and Corollary 4.6.12. Its module is
`Sheaf.CategoryTheory.DiscreteFibration`; its declaration is
`CategoryTheory.Functor.IsDiscreteFibration`. The real Prop-valued definition uses
`∃!` over a dependent pair and source equality transport. Searches across DAG, blueprint,
Mathlib, upstream, and side Lean found no existing definition; semantic hits concern
weaker general fibered functors. All search records include actual results, and the new
node is cited by the item's `stmt_deps`. It has no theorem or postponed construction.

## Second reading by NY

I reread the node, its dependency declaration, the two delivered modules, and Cisinski's
source at Lemma 4.6.9, Proposition 4.6.11, and Corollary 4.6.12 (printed pp. 179--183).
The item statement's objects and hypotheses render as follows, with no mismatch found:

- The small ordinary categories and functors are `E D B : Cat.{u, u}`, `U : E ⟶ B`,
  and `V : D ⟶ B`; the explicit universe `u` is the fixed size convention used by the
enhanced-diagram dependency. No finiteness, nonemptiness, or extra category structure
  is assumed.
- For each `b`, the comma category `(U ↓ b)` is
  `CostructuredArrow U.toFunctor b`; its objects and arrows therefore have exactly the
  displayed `Ue ⟶ b` and commuting-arrow data. Postcomposition by each
  `β : b₀ ⟶ b₁` is `CostructuredArrow.map (S := U.toFunctor) β`, and `hU` requires
  weak homotopy equivalence of its nerve map for every such arrow.
- The discrete-fibration hypothesis is `hV : V.toFunctor.IsDiscreteFibration`, whose
  definition quantifies over every `d`, `b`, and `β : b ⟶ V.obj d`, and uses `∃!` on
  the dependent pair `Σ d', d' ⟶ d` together with the transported equality
  `eqToHom h.symm ≫ V.map l.2 = β`. This is the source's strict uniqueness, including
  the lifted domain.
- The strict pullback is Mathlib's `pullback U V` in `Cat`; its projections are used by
  `quillenBBaseChangeComparison`, and the comparison's two endpoint coordinates are
  the nerves of those projections. Thus the displayed nerve square is the exact strict
  pullback square from the node.
- `quillenBNerveFunctor` is the functorial `Sing |N(-)|` replacement. The path model
  `quillenBPathPullback U V` is the iterated pullback along endpoint evaluations of
  `Fun(Δ[1], RN(B))`, with `quillenBPathFst`, `quillenBPathSnd`, and
  `quillenBPathEdge` retaining all three specified coordinates. The first conclusion
  conjunct is precisely weak equivalence of the actual constant-path comparison.
- The second conjunct quantifies over every second triple with the same `hU` and
  discrete-fibration hypotheses, every strictly commuting `a`, `b`, `c` (the equations
  `hu` and `hv`), and supplies `t`. Its three coordinate equations and final equation
  with `pullback.map` state the node's naturality of the specified comparison, rather
  than an unspecified abstract equivalence. The no-extra-axioms sentence in the node
  introduces no Lean hypotheses and no such hypotheses occur in the theorem.

Edge cases were checked against these definitions: empty `D`, empty `E`, and empty `B`
remain allowed; the lift predicate is vacuous when appropriate; identity functors and
zero-arrow/identity cases use the same strict equations; and no characteristic,
Noetherian, invertibility, or hidden nonemptiness assumption appears. The single universe
parameter is explicit and is shared by the `Cat` and `SSet` constructions as required by
the dependency's size convention.

For the one-definition check I repeated the recorded LeanSearch, LeanFinder, Loogle, and
grep searches for discrete fibrations, Quillen B, comma nerves, and homotopy pullbacks in
Mathlib, the upstream `WeilConjectures` tree, the side `lean/Sheaf` tree, and the DAG.
Only Mathlib's weaker `IsFibered`/`IsPreFibered` notions and unrelated nerve or model
category results were found. No existing declaration states this theorem or the strict
unique-lift predicate. The source PDF confirms that the overcategory dual of Proposition
4.6.11 and Corollary 4.6.12 supplies exactly the comma-transition and right-fibration
orientation used here.

No mismatch was found, so no statement, dependency, or definition was changed in the
second reading. Both delivered modules were compiled separately with `scompile.py`; the
only `sorry` is the item's postponed theorem, with its complete proof plan and matching
DAG node. The node's `lean.statement` is verbatim the theorem signature.
