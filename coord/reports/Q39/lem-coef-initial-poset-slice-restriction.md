## Worker report

The module `Sheaf.CategoryTheory.InitialPosetSliceRestriction` states the original
node, with its proof left as the single named theorem
`SSet.Enhanced.initialPosetSliceRestriction := by sorry`. Its two helper definitions
have real data: `fullJoinSlice` is the pullback of the recorded join-slice source
projection along the recorded full-subcomplex inclusion, and `initialVertex` is
the Yoneda map corresponding to the zero-simplex `ComposableArrows.mk₀ ⊥`.
All three declarations are listed in `lean.declarations`. No new node or dependency
repair is needed.

The saved packet replaced canonical restriction by existence of an unspecified
map and recorded a statement correction. That weakened the source statement.
This repair restores the repository node verbatim outside its `lean` field and
adds the exact component formula to the theorem. For every degree `n` and source
simplex `s`, the join extension of `r(s)` is
`orderedJoinFunctor.map (𝟙 (stdSimplex.obj n.unop), initialVertex) ≫ s.extension`.
Thus `r` is restriction along `id ⋆ initialVertex` on the entire simplex, including
its pure blocks. Its separate source equation fixes the other pullback coordinate.
These equations uniquely determine the map: a `JoinSliceSimplex` is determined by
its base and extension, and the two pullback projections are jointly monic. The
existential statement specifies the canonical restriction, without choosing data
from a mere existence theorem or introducing an arbitrary map. No statement
correction remains and no citer changes meaning.

Every hypothesis and clause is rendered as follows:

- A small poset `T` with least element `t` is `{T : Type u} [PartialOrder T]
  [OrderBot T]`; `t` is `⊥`. Equipping a poset having a least element with this
  structure adds no mathematical assumption and excludes no choice of least
  element, since it is unique.
- The quasicategory is `(E : SSet.{u}) [Quasicategory E]`.
- The full subcategory is `(P : E _⦋0⦌ → Prop)` interpreted by the dependency's
  `fullSubcomplex E P`, containing exactly the simplices all of whose vertices
  satisfy `P`. The redundant `fullSliceSubcomplex` alias in the saved packet was
  removed; there is only the dependency's full-subcategory definition.
- The coherent diagram is `(p : nerve T ⟶ E)`.
- The join slice is precisely the dependency's `joinSlice p`, with its stored
  extension `Δ[n] ⋆ nerve T ⟶ E`; the dependency also imposes the right-block
  restriction and all simplicial operator equations.
- `E₀,/q = E₀ ×_E E_/q` is `fullJoinSlice P q`, defined using
  `pullback (fullSubcomplex E P).ι (joinSliceProjection q)`.
- `p(t)` as a point diagram is `initialVertex (T := T) ≫ p`. The theorem's
  map has exactly the required domain and codomain.
- Restriction along the least vertex is the displayed extension formula in
  every `n : SimplexCategoryᵒᵖ` and every `s : (fullJoinSlice P p).obj n`.
  It retains all higher simplices, not just vertices or homotopy classes.
- Being over `E₀` is the first conjunct, `r ≫ pullback.fst ... = pullback.fst ...`.
- Being a trivial Kan fibration is `modelCategoryQuillen.I.rlp r`. By the
  dependency's recorded Mathlib match, `I` is the family of all boundary
  inclusions, including `∂Δ[0] → Δ[0]`; its dimension-zero lifting condition is
  exactly surjectivity on vertices.
- Every inclusion `L ⊆ M` is represented invariantly by `∀ L M : SSet.{u},
  ∀ j : L ⟶ M, Mono j →`. A simplicial monomorphism is a degreewise inclusion
  after identifying its source with its image.
- Prescribed data are `h : L ⟶ fullJoinSlice P p` and
  `v : M ⟶ fullJoinSlice P (initialVertex ≫ p)` with `h ≫ r = j ≫ v`.
  The final existential supplies `c` with `j ≫ c = h` and `c ≫ r = v`.
- Every source simplex is fixed: composing the last equation with the target's
  source projection and using the first conjunct identifies the lift's source
  with the source of `v` in every degree. `j ≫ c = h` fixes the entire boundary.
- All data and test simplicial sets lie in the common containing universe `u`.
  There are no limit or colimit assumptions on the quasicategory or its full
  subcategory; the pullback is formed in the category of simplicial sets.

Dependency declarations and sources read:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, with its full signature, docstring, and vertex
  condition; this is `def-cbc-enhanced-diagrams-cones`.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`:
  `SSet.Enhanced.JoinSliceSimplex`, `joinSlice`, `joinSliceProjection`,
  `joinStandardFunctor`, `orderedJoinInl`, `orderedJoinInr`, and
  `joinSlice_right_fibration`, including their full definitions and docstrings;
  these supply `lem-coef-infinity-slice-right-fibration`.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation` (publicly provided by that
  dependency): `SSet.Enhanced.orderedJoinFunctor`, its ordered-block convolution
  formula and its action on maps.
- `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.I` and `rlp_monomorphisms`; and
  `Mathlib.AlgebraicTopology.SimplicialSet.Boundary`: `SSet.boundary` and
  `boundary_zero`. Together with `CategoryTheory.MorphismProperty.rlp`, these
  are the recorded match of `def-weil-pbc-trivial-kan-fibration`.
- The already-stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.ConeMonoRightAnodyne`
  (`SSet.rightAnodyneExtensions_rightCone_map`) and
  `Sheaf.AlgebraicTopology.AnodyneCocones` (`SSet.Enhanced.anodyne_cocones`).
  The theorem docstring expands all eight DAG proof steps, including reversal,
  the explicit poset-cone retract, the pushout join, gluing, extension closure,
  the source pullback, and the zero-dimensional boundary condition.

Edge cases checked: for the singleton poset the restriction is induced by the
isomorphism from its single vertex, and the component formula gives its actual
map. For a two-element chain in an ordinary-category nerve, an arrow to the least
value extends uniquely by composition; this checks the orientation. An empty full
subcategory gives empty source and target slices and imposes no nonemptiness
hypothesis. `L` and `M` can be empty, and `j` can be an identity or any degreewise
inclusion. The `n = 0` boundary is empty and its filler is vertex surjectivity.
An empty indexing poset has no least element and is correctly excluded. There
are no disputed statements or remaining node faults.

Searches retained from the previous packet and repeated for the repair:

- LeanFinder, via `msearch.py Q39 lem-coef-initial-poset-slice-restriction`, query
  `The canonical restriction of quasicategory join slices to a least vertex is a
  trivial Kan fibration and fixes every simplex in its full source subcategory`:
  eight hits (`SSet.modelCategoryQuillen.I`, `.J`, nerve quasicategory and strict
  Segal results, and cylinder projection formulas), none stating this theorem.
- Loogle, query `"Quasicategory", "join"`: zero hits.
- Mathlib grep, query `joinSlice|initialPosetSliceRestriction|join.*restriction`
  under `AlgebraicTopology`: zero hits.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for
  `initialPosetSliceRestriction|fullJoinSlice|initialVertex` and the node id:
  zero hits. `rg` with those declaration names throughout Mathlib: zero hits.
- `rg` in the project's `lean/Sheaf/CategoryTheory` for ordered joins and slice
  restrictions found the dependency definitions above and the unrelated
  `JoinSliceCoconeComparison` naturality predicate. That predicate restricts
  cocones with the variable block on the other side and does not state the
  initial-poset restriction theorem. The helper names are absent from the
  published project. No exact existing theorem was found.
- Earlier searches saved on the node include LeanFinder queries on initial
  cone restriction and left-anodyne slice restriction, Loogle queries for
  `Quasicategory` with `TrivialFibration`, `Under`, and `cone`, and Mathlib grep
  for left/right-anodyne joins. The generic boundary, horn, nerve and ordinary
  cone results found there do not supply this theorem.

Validation: the repaired statement, including its component formula and explicit
trivial-Kan clause, compiled cleanly through `scompile.py`; the final dry run
checks the packet against the current server state. The separate second reader
still performs the independent reading and delivery.


## Earlier second reading (a previous round; superseded)

Pending the separate second reader required by the worker brief. This packet
contains the author's statement and self-check; no independent reading is claimed
here. The second reader must replace this marker with their clause-by-clause
review before delivery.


The first completed dry run found only packaging diagnostics: its signature
extractor excludes the final `:=`, and it requires the second-reading heading.
The Lean record now follows that extractor, and the heading above explicitly
marks the independent reading as pending. The original node statement is intact.

Literature: WANTED archival copies of HTT Proposition the project server and Proposition
the project server(a), and Kerodon 018J, 018F, 02J5, and 0196, as requested in the node's
retained stage-1 proof-origin record. The node already contains the source URLs
and the complete eight-step proof.

## Second reading by Q39

I read the node `lem-coef-initial-poset-slice-restriction`, its source place, the
three statement dependencies, and
`lean/Sheaf/CategoryTheory/InitialPosetSliceRestriction.lean` independently.
The source place is Joyal, HTT Proposition the project server (PDF p. 79, the case
`π = id` and a left-anodyne least-vertex inclusion), with the same restriction
used in Proposition the project server(a) (PDF p. 428). The source proposition says that
the induced map of join slices is a trivial Kan fibration; the displayed
boundary lifting clause is its relative form.

The node's objects and hypotheses match the Lean as follows.

- The small partially ordered set `T` and its least element `t` are
  `{T : Type u} [PartialOrder T] [OrderBot T]`, with `t` rendered by
  `(⊥ : T)` in `initialVertex`. `OrderBot` supplies a least element, and its
  uniqueness means choosing `⊥` does not add a hypothesis or remove a case.
- The quasicategory `\mathcal E` is `(E : SSet.{u}) [Quasicategory E]`.
- The full subcategory `\mathcal E_0` is the predicate
  `(P : E _⦋0⦌ → Prop)` and the dependency declaration
  `fullSubcomplex E P`; its definition requires `P` on every vertex of every
  simplex, exactly the full-subcategory convention in the node.
- The coherent diagram `p : N(T) → E` is
  `(p : nerve T ⟶ E)`. The common universe `u` is the fixed containing
  universe for `T`, `E`, the subcomplex, and all test simplicial sets.
- The join slice `E_{/p}` is the dependency's `joinSlice p`, whose
  `JoinSliceSimplex.extension` is a map from `Δ[n] ⋆ nerve T` to `E` and whose
  `restrict_right` equation fixes the `p` block. The source projection is
  `joinSliceProjection p`.
- The pullback `E_{0,/p}` is exactly
  `fullJoinSlice P p := pullback (fullSubcomplex E P).ι
  (joinSliceProjection p)`. The same definition with
  `initialVertex ≫ p` gives `E_{0,/p(t)}`.
- The least-vertex inclusion `{t} → N(T)` is the real-data definition
  `initialVertex : Δ[0] ⟶ nerve T`, obtained from the Yoneda image of
  `ComposableArrows.mk₀ (⊥ : T)`.

The conclusion is rendered clause by clause. The existential map
`r : fullJoinSlice P p ⟶ fullJoinSlice P (initialVertex ≫ p)` is followed by
the equality
`r ≫ pullback.fst ... = pullback.fst ...`, which says that restriction is over
the full source subcategory `E_0`. For every degree
`n : SimplexCategoryᵒᵖ` and every simplex `s` of the source pullback, the next
conjunct gives
```
targetExtension (r.app n s) =
  orderedJoinFunctor.map (𝟙 (stdSimplex.obj n.unop), initialVertex) ≫
    sourceExtension s
```
This is precomposition by `id ⋆ initialVertex`, so it specifies the canonical
restriction on the complete join simplex, including all pure and mixed faces;
it is stronger than an unspecified existential map but exactly the map in the
node. The conjunct `modelCategoryQuillen.I.rlp r` is the Mathlib encoding of
the node's trivial Kan fibration: `I` is the family of all boundary inclusions,
including the empty `∂Δ[0]`, so it includes vertex surjectivity. Finally, for
every `L`, `M`, map `j : L ⟶ M` with `Mono j`, boundary map `h`, and target map
`v`, the compatibility equation is rendered as `h ≫ r = j ≫ v`; the existential
`c : M ⟶ fullJoinSlice P p` has `j ≫ c = h` and `c ≫ r = v`. These are the
prescribed-boundary and prescribed-source lifting clauses in the same order as
the node. No limits or colimits in `E` or `E_0` occur as hypotheses.

I checked the edge cases explicitly. `OrderBot` excludes an empty `T`, as the
node does because an empty poset has no least element. A singleton `T` makes
`initialVertex` the sole vertex and the formula the identity restriction. A
two-element chain in the nerve of an ordinary category gives the expected
composition with the arrow from the least vertex. `P` may be empty, so both
pullback slices may be empty; `L` and `M` may be empty, and `j` may be an
identity or any simplicial monomorphism. The `n = 0` boundary is empty and is
handled by the `I` clause's vertex-surjectivity condition. The definition and
theorem use one arbitrary universe `u` and impose no characteristic, finiteness,
Noetherian, or nonemptiness hypothesis beyond the stated least element.

For duplicate-definition searches I reran LeanFinder through
`msearch.py Q39 lem-coef-initial-poset-slice-restriction`, with queries for
initial-poset join-slice restriction and coherent cone restriction; all hits
were generic horn, nerve, or model-category declarations. Loogle queries for
`"Quasicategory", "join"`, `"Quasicategory", "TrivialFibration"`, and
`"Quasicategory", "Under"` found no matching theorem. Grep over Mathlib's
`AlgebraicTopology` and over `WeilConjectures/` found no
`initialPosetSliceRestriction`, `fullJoinSlice`, or `initialVertex`. Grep over
the project's `lean/Sheaf` found only the recorded generic join-slice and
full-subcomplex dependencies; no declaration states this restriction theorem.
The existing `orderedJoinFunctor` is used from its recorded dependency rather
than redefined.

No mismatch was found in this second reading, so no source statement, helper,
dependency, or Lean signature was changed. The only delivery edit is this
independent review section. The module compiles cleanly with the required
`scompile.py` wrapper; the sole allowed warning is the postponed theorem proof.
