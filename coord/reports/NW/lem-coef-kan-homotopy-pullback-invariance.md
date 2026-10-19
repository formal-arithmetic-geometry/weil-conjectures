## Worker report

Reconstructed the delivery from the DAG after the previous attempt left no node copy,
module, or report. The item is stated in
`lean/Sheaf/CategoryTheory/KanHomotopyPullbackInvariance.lean`.
Its only postponed theorem is
`SSet.Enhanced.kan_homotopy_pullback_invariance`, with proof `sorry`.
`SSet.Enhanced.simplicialHomotopyPullbackMap` has real data, constructed by two
`pullback.lift`s; there is no postponed construction or arbitrary comparison map.
The node copy changes only `lean`; there are no new nodes or dependency repairs.
No maintenance repair note for this item was present in `coord/repair-notes/`.

Source read: [Kerodon Proposition the project server, Tag 032B](https://kerodon.net/tag/032B)
and [Construction the project server, Tag 010B](https://kerodon.net/tag/010B), online.
The proposition gives invariance under the three vertical weak equivalences, and
Construction 010B specifies the endpoint path model. The node asks for all six
objects to be Kan; the Lean retains exactly those assumptions. The source itself
allows more general endpoint objects, but that stronger generalization is not
silently substituted for the node. No source or statement correction is needed.

Hypothesis and clause correspondence:

- The fixed simplicial universe is `universe u`, with all six objects bound as
  `U V W U' V' W' : SSet.{u}`. These are arbitrary simplicial sets in that universe.
- The maps of Kan complexes are `u : U ⟶ W`, `v : V ⟶ W`,
  `u' : U' ⟶ W'`, `v' : V' ⟶ W'`, together with the six separate
  `[KanComplex ...]` binders. In particular none of the four endpoint Kan
  assumptions is omitted, and no inhabitedness is required.
- The three comparison maps are the binders `a`, `b`, `c` with the exact sources
  and targets in the node.
- Their three weak homotopy equivalence assumptions are `ha`, `hb`, `hc`, each
  using `SSet.Enhanced.IsWeakHomotopyEquivalence`. This is the dependency's
  realization-based component and positive based cubical homotopy-group condition,
  not an unrelated model-category weak-equivalence predicate.
- The two strict equations `cu = u'a` and `cv = v'b` are `hu : u ≫ c = a ≫ u'`
  and `hv : v ≫ c = b ≫ v'`; Lean composition is written in diagram order.
- `Fun(Δ¹,W)` is `(ihom Δ[1]).obj W`. Endpoint zero and endpoint one are the
  existing `evaluation Δ[1] W (stdSimplex.obj₀Equiv.symm 0)` and the analogous
  expression with `1`. The source of the helper map is the nested pullback
  `pullback (pullback.snd u ev₀ ≫ ev₁) v`. It retains the first endpoint object,
  the entire internal-hom path simplex, and the last endpoint object; its two
  equations are precisely `ev₀(γ) = u(x)` and `ev₁(γ) = v(y)`. The target is
  the identical expression with primed objects and maps.
- The inner `pullback.lift` has projections `pullback.fst ... ≫ a` and
  `pullback.snd ... ≫ (ihom Δ[1]).map c`. The outer lift has that inner map
  composed with its first projection, and `pullback.snd ... ≫ b` as its last
  projection. Thus its coordinates are exactly `(a(x), b(y), c ∘ γ)`, in every
  simplicial degree. Its compatibility proofs use naturality of `evaluation`
  and the two supplied strict equations. It is defined even without the Kan
  and weak-equivalence assumptions, as a canonical map must be.
- The conclusion is exactly
  `IsWeakHomotopyEquivalence (simplicialHomotopyPullbackMap a b c hu hv)`.
  No existential replacement of the prescribed map, chosen homotopy, extra
  conclusion, or additional assumption appears.

Dependencies read and used:

- `def-cbc-enhanced-diagrams-cones`: read the statement, complete `lean` record,
  and the docstrings/signatures in `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
  In particular this file uses its `SSet.Enhanced.IsWeakHomotopyEquivalence`
  and `SSet.Enhanced.evaluation` directly. Mathlib supplies `SSet`, `KanComplex`,
  `stdSimplex`, `ihom`, and categorical pullbacks, as prescribed by that node.
- For the proof plan, `lem-coef-sset-anodyne-pushout-product` has exact Mathlib
  match `SSet.anodyneExtensions_pushoutObjObjι` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`,
  lines 95–103, read in source and imported non-publicly.
- The other currently recorded proof dependency is
  `SSet.realization_finite_limits` in
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits`, imported non-publicly.
  Its full recorded signature and source docstring were read. The Kan-target
  testing and strict-pullback invariance nodes currently have no Lean records;
  they are proof prerequisites, not prerequisites needed to type this statement.
  The docstring follows all five DAG proof steps, with the corresponding nodes.

Edge cases checked against the construction and statement:

- Empty Kan complexes remain allowed. If either endpoint object is empty, the
  nested pullback is empty. A weak equivalence with an empty source forces the
  corresponding target realization to have no components. No basepoint or
  nonempty hypothesis is introduced.
- If `W` is empty, maps into it force the source endpoints to be empty; the
  definitions still type without any choice of points.
- For singleton bases, endpoint evaluations impose only the unique base
  equations, and the model is the product of the endpoints; the displayed map
  has exactly the product coordinates. Constant simplicial discrete Kan
  complexes give the ordinary fiber product, with no artificial paths.
- Identity cospan maps act by identities on all three projections. The
  construction retains all higher simplices rather than taking components.
- The weak-equivalence predicate includes components and all positive degrees,
  with all realization basepoints; dimension zero and the empty case are not
  replaced by an inappropriate homotopy-group-only condition.
- Every universe and variable is explicit; `autoImplicit` is false. There is no
  file-local notation or instance used to interpret the exported statement.

Searches actually run for this attempt:

- `msearch.py ... leanfinder` with query
  `Weak equivalences of spans of Kan complexes induce weak equivalences of path space homotopy pullbacks`:
  eight hits, consisting of `PathObject` projection weak equivalences,
  fibrancy/fibration instances, `instIsGoodTrans`, and
  `PathObject.RightHomotopy.weakEquivalence_iff`. Read the path-object source:
  these refer to abstract path objects or individual projections and do not
  assert the specified three-map invariance of this endpoint path pullback.
- `msearch.py ... loogle` with query `"PathObject", "pullback"`: zero hits.
- `msearch.py ... grep` with query
  `homotopyPullback|homotopy_pullback|pathPullback` in `AlgebraicTopology`:
  zero hits.
- `msearch.py ... leansearch` with query
  `Weak equivalences between commutative cospans of Kan complexes induce a weak equivalence on their path space homotopy pullbacks`:
  eight hits: generic weak-equivalence predicates, over-category compatibility,
  path-object constructor/no-confusion declarations, and
  `CofibrantObject.weakEquivalence_toHoCat_map_iff`; no exact statement.
- `rg` for `homotopyPullback|homotopy_pullback|pathPullback` in the upstream
  `WeilConjectures/` and project `lean/Sheaf/`: no upstream match; the project
  has the constant-path comparison in `RelativeInfinityCone.lean` and unrelated
  derived-category pullback squares. Read `RelativeInfinityCone.lean` and its
  referenced `SourceAttachmentGluing.lean`: `simplicialHomotopyPullback` there
  is precisely the same nested categorical pullback expression. This delivery
  introduces no duplicate definition of that object: the map's domain and codomain
  use the categorical expression directly, without importing the much broader
  source-attachment theorem. The existing constant-path map has a different
  domain and different mathematical role from this three-corner change map.
- `rg` for the exact item ID in upstream `WeilConjectures/`: no hit.
- `rg` for `simplicialHomotopyPullbackMap|kan_homotopy_pullback_invariance`
  in upstream, Mathlib, project `lean/Sheaf/`, and `dag/lean_names_upstream.json`:
  no pre-existing declaration with either proposed name.

Validation: the prescribed `scompile.py` compiled both the sandbox form and the
library module form cleanly, with no warnings, after line wrapping. No global
build, direct Git command, or modification of a read-only repository was made.
The theorem remains `sorry`, as required for stage 2. The node's `lean.statement`
is extracted verbatim from the theorem keyword through the end of its signature.
The delivery dry run is the final worker validation; the independent second reader
will write their own section and deliver.

## Second reading by NW

I independently opened the node, its Kerodon source places, the dependency records,
and `KanHomotopyPullbackInvariance.lean`. The source is Kerodon Proposition the project server
(tag 032B), whose displayed diagram has two cospans and three vertical weak
equivalences, together with Construction the project server (tag 010B), which defines the
homotopy fiber product as the endpoint-evaluation iterated pullback. The node
deliberately specializes the proposition to six Kan objects; the Lean retains that
specialization exactly.

The item-by-item correspondence is:

* The six objects `U V W U' V' W' : SSet.{u}` are the two endpoint cospans in the
  node, all in one explicit universe `u`.
* The four cospan maps are the binders `u : U ⟶ W`, `v : V ⟶ W`,
  `u' : U' ⟶ W'`, and `v' : V' ⟶ W'`; the six `[KanComplex ...]` binders render
  the node's “maps of Kan complexes” assumption without adding inhabitedness.
* The vertical maps are exactly `a : U ⟶ U'`, `b : V ⟶ V'`, and
  `c : W ⟶ W'`. Their weak-equivalence hypotheses `ha`, `hb`, and `hc` use the
  recorded `SSet.Enhanced.IsWeakHomotopyEquivalence` predicate.
* The strict commutativity clauses `cu = u'a` and `cv = v'b` are rendered in
  diagram-order categorical composition by `hu : u ≫ c = a ≫ u'` and
  `hv : v ≫ c = b ≫ v'`.
* `simplicialHomotopyPullbackMap` has as domain
  `pullback (pullback.snd u ev₀ ≫ ev₁) v` and the identical primed codomain,
  where `ev₀` and `ev₁` are the existing `evaluation Δ[1]` maps at the standard
  simplex vertices `0` and `1`. This is exactly
  `U ×_{W,ev₀} Fun(Δ¹,W) ×_{ev₁,W} V` and its primed analogue. Its two nested
  `pullback.lift`s give the coordinates `(a(x), b(y), c ∘ γ)`; the endpoint
  naturality equalities and `hu`, `hv` prove the required pullback equations.
* The conclusion is exactly
  `IsWeakHomotopyEquivalence (simplicialHomotopyPullbackMap a b c hu hv)`, with
  no existential map, weakened predicate, or extra conclusion.

The edge cases remain covered: empty Kan objects and empty pullbacks type without
any nonemptiness assumption; an empty base forces the relevant endpoint maps to
have empty domains; identity cospans and identity vertical maps give the identity
coordinate map; a terminal or singleton base reduces to the expected product; and
all dimension-zero and higher path simplices are retained. No index set, integer
parameter, characteristic, or additional universe is present. The path pullback
formula agrees definitionally with the existing `simplicialHomotopyPullback` used
elsewhere in the project, while this module introduces only the new comparison map.

I reread the recorded `def-cbc-enhanced-diagrams-cones` declaration and its
`evaluation` and `IsWeakHomotopyEquivalence` helpers, and checked the proof-only
records `lem-coef-sset-anodyne-pushout-product`,
`lem-cbc-realization-weak-equivalence`, `lem-coef-realization-finite-limits`, and
`lem-coef-kan-pullback-fibration-invariance`. Their interfaces are used as recorded;
the latter three have no Lean declaration yet where the node records none, so no
dependency module or new definition node is needed in this delivery. I searched
Mathlib, the upstream `WeilConjectures/` tree, and project `lean/Sheaf/` for the
item, the helper name, and homotopy/path-pullback variants (LeanFinder/LeanSearch,
Loogle, and `rg`); only the unrelated existing path-pullback object and comparison
were found. They do not state this three-map invariance theorem, so no `existing`
record applies.

No mismatch was found and no file or node field required repair. The module was
compiled with the prescribed `scompile.py`; it completed for both the sandbox and
library forms with no errors or warnings other than the permitted theorem `sorry`.
