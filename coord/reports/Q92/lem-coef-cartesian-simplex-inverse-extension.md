## Worker report

The module `lean/Sheaf/AlgebraicTopology/CartesianSimplexInverseExtension.lean`
states `SSet.Marked.Over.cartesian_simplex_inverse_extension` with `sorry`.
It introduces no new definitions and changes only the item's `lean` record.
The statement is unchanged. There are no disputed statements or dependency faults.

Source read: Lurie, Higher Topos Theory, Proposition the project server, proof (3) implies (2),
printed pages 156–157, downloaded to this sandbox as `HTT.pdf` and read as `HTT.txt`.
The source prescribes the boundary inverse and cylinder before extending across the
simplex; for positive dimension every vertex lies in the boundary. The node supplies
the detailed marking verification in addition to this source argument. The complete
11-step node proof, including every cited node, is in the theorem docstring.

Hypothesis and conclusion correspondence:

- `n : ℕ` and `hn : 1 ≤ n` render the positive-dimensional simplex hypothesis.
- `X Y : Over (Δ[n] : SSet.{u})` render the two small marked total spaces and their
  maps to the common simplex. `Over` is the actual category over the sharp base.
- `hX : IsNaturallyFibrant false X` and the corresponding `hY` assert cartesian
  fibrations with exactly their cartesian edges marked. This packages the two
  fibration hypotheses together with their natural markings, using the recorded
  arbitrary-base horn definitions; it does not assume a relative model structure.
- `f : X ⟶ Y` is the marked map over the simplex, with its base equality bundled.
- `hf` says `Enhanced.IsFunctorEquivalence (fiberMap f s)` for every vertex `s`.
  Vertices of `Δ[n]` are precisely the `n+1` vertices indexed by `0 ≤ i ≤ n`.
  The fiber map is the recorded canonical strict pullback map, and the equivalence
  predicate specifies a coherent quasi-inverse and both inverse equivalences.
- `pullObject (boundary n).ι X` and the corresponding term for `Y` are precisely
  the boundary pullbacks with the pulled-back markings. The existing pullback
  construction orders its factors as boundary ×_simplex X; the canonical swap
  identifies this with the node's X ×_simplex boundary.
- `rBoundary` is the specified marked boundary inverse over the boundary.
- `hBoundary` is the specified 1-simplex of the relative sharp mapping complex
  on the boundary pullback of X. `hBoundary₀` fixes its source at
  `mapVertex ((pull (boundary n).ι).map f ≫ rBoundary)` and `hBoundary₁` fixes its
  target at the identity. Thus both the homotopy and its endpoints are prescribed.
- The existential `r : Y ⟶ X` is the marked inverse map over the whole simplex;
  `h : (mapSharp X X) _⦋1⦌` is the whole-simplex sharp mapping edge.
- The first two conclusion equations fix its source at `f ≫ r` and its target at
  `𝟙 X`. CategoryTheory composition reads left to right, so `f ≫ r` is `r f`.
- `(pull (boundary n).ι).map r = rBoundary` fixes the boundary restriction exactly.
- The last equation fixes the entire boundary cylinder exactly: precompose
  `h.left.val` by the boundary pullback projection whiskered with `Δ[1]`, and
  equate it to `hBoundary.left.val` followed by the boundary projection into X.
  Both sides have domain X_boundary × Δ[1] and codomain X. Since the boundary
  inclusion is a monomorphism, its pullback projection is a monomorphism, and
  the base map is already fixed, this is exactly equality of the restricted
  boundary edge. It checks every simplicial degree, not merely endpoints or
  homotopy classes. Marked maps have proof-irrelevant marking and base witnesses.
- No interior inverse or homotopy occurs in the hypotheses. There is no extra
  right inverse or second interior homotopy in the conclusion.

Dependency declarations read and reused:

- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.cartesianNatural`, `cartesianNaturalOver`, and
  `SSet.Marked.Over.relative_marked_anodyne_calculus`, including the sharp-core
  and natural-pullback clauses. This module exports the underlying interfaces
  from `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `Over.IsNaturallyFibrant`, `Over.relativeFibration`,
  `Over.IsDistinguishedEdge`, `Over.mapSharp`, `Over.mapVertex`,
  `Over.pullObject`, `Over.pull`, `Over.fiberMap`, and `Over.productLeft`.
  Their complete source definitions were read. The arbitrary-base cartesian
  condition uses the final-horn criterion from `InfinityFibrations`.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence`, `AreNaturallyEquivalent`,
  `IsEquivalenceEdge`, `diagramVertex`, and `core`; their source definitions and
  docstrings were read. The broad node's primary declaration `coneCategory`
  is not needed for this particular lemma.
- Mathlib standard simplex, boundary, pullback, and monoidal whiskering are used
  directly. No notion was copied or replaced.

All recorded proof-dependency modules are imported without `public`, except the
statement-dependency imports, which are public. The two Mathlib homotopy-class
leaves are imported through `Mathlib.AlgebraicTopology.ModelCategory.Homotopy`
and `RightHomotopy`. Three proof-only nodes currently lack recorded Lean modules:
`lem-coef-infinity-full-essential-image`, `lem-coef-all-cofibrant-left-proper`,
and `lem-coef-infinity-cocartesian-mapping-criterion`. Their future proof imports
are left to maintenance under stage 2 rule 7; none is needed to type this statement.

Edge cases checked before writing:

- `n=1`: both vertices lie in the two-component boundary; the input homotopy
  specifies every vertical vertex edge, but no interior edge or inverse.
- `n=0` is expressly excluded by the node, retained as `1 ≤ n` rather than
  silently using a successor index or an extra premise.
- Empty total spaces or empty vertex fibers are allowed by the binders. No
  `Nonempty` or connectedness instance is required. A coherent equivalence
  involving an empty fiber has exactly its usual force.
- Degenerate edges stay marked in the existing Marked structure; the natural
  marking hypothesis identifies them with cartesian edges too.
- Noninjective f is allowed: no monomorphism hypothesis on f was introduced.
- Nonconstant boundary paths are preserved as complete specified cylinders.
- All simplicial objects are in the explicitly bound arbitrary universe `u`;
  no additional universe equality or restriction is imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A fiberwise equivalence of cartesian fibrations
  over a simplex has a marked homotopy inverse extending a specified inverse
  and homotopy on the boundary”; eight hits, concerning relative simplicial
  homotopy identities, truncated products and general model homotopy calculus;
  none states this relative cartesian simplex extension. The search log also
  records the previous worker's compatible queries and their results.
- `msearch.py ... loogle "SSet.RelativeMorphism.Homotopy"`: twelve hits for
  Mathlib relative unmarked homotopies, not the prescribed marked sharp path
  extension across a cartesian simplex.
- `msearch.py ... grep "cartesian.*inverse|inverse.*cartesian|homotopy.*extension"
  AlgebraicTopology`: two hits for general right-homotopy extension in model
  categories, not this statement.
- `rg` with the cartesian/inverse pattern in the upstream `WeilConjectures` and
  shared `lean/Sheaf` trees: scheme and sheaf inverse constructions, and this
  item's citation in the relative model proof; no existing declaration.
- Search for the exact node id in upstream `WeilConjectures`: no hit.
  The shared Lean hit is a proof docstring citation in
  `MarkedRelativeCartesianModel`, not a declaration of the simplex lemma.

Validation: `scompile.py Q92 lem-coef-cartesian-simplex-inverse-extension` compiled
this file against the current overlay and library with no errors or warnings.
Every variable and the universe are explicit; autoImplicit is disabled.
The only postponed theorem is the item itself; there are no additional sorries.
An independent second reading is to be supplied by the next worker, as instructed.

## Second reading by Q92

Independent second reader, 2026-10-17. I opened the node, the complete Lean module,
the two statement-dependency node records and their Lean declarations, and HTT
Proposition the project server, proof (3) implies (2), printed pp. 156–157, in `HTT.txt`.
This source is HTT, not Stacks; there is no Stacks source place for this item.
The source assumes both maps to the base are cartesian fibrations, and its simplex
induction prescribes the boundary inverse and homotopy before extending them.
The node isolates its positive-dimensional case, and explicitly requires marked
maps and a sharp mapping edge. No source-wide ring, scheme, or finiteness hypothesis
is relevant. There is no `statement_change`, repair note, new definition node, or
dependency module in this delivery.

My object/hypothesis/conclusion checklist, matched independently against the Lean:

1. A positive integer dimension and its standard simplex: `(n : ℕ) (hn : 1 ≤ n)`
   and `(Δ[n] : SSet.{u})`. Exact; dimension zero is excluded by the node itself.
2. Two small cartesian fibrations with their natural markings:
   `(X Y : Over (Δ[n] : SSet.{u}))`, `hX : IsNaturallyFibrant false X`, and `hY`.
   Exact. I read `Over`, `relativeFibration`, `IsDistinguishedEdge`, and
   `IsNaturallyFibrant` in `MarkedRelativeCartesianModel`. `Over S` is the marked
   slice over `sharp S`; the predicate says inner fibration, a cartesian lift of
   each edge with prescribed target, and marking iff final-horn cartesian.
   It assumes neither a model structure nor extra quasicategory instances.
3. A marked map over the simplex: `(f : X ⟶ Y)`. Exact: `Marked.Hom` requires
   marking preservation and the slice morphism includes the base equation.
4. An equivalence on every vertex fiber: `hf : ∀ s : (Δ[n] : SSet.{u}) _⦋0⦌,
   Enhanced.IsFunctorEquivalence (fiberMap f s)`. Exact. I read `fiberMap`,
   `Enhanced.fiber`, `IsFunctorEquivalence`, `AreNaturallyEquivalent`, and
   `IsEquivalenceEdge`: the map is the strict pullback map over the vertex and
   the predicate gives a quasi-inverse with coherent natural inverse equivalences.
   The vertices of this simplex are exactly `Fin (n + 1)`; no vertex is omitted.
5. Boundary pullbacks with pulled-back markings and the restricted map:
   `pullObject (boundary n).ι X`, its `Y` counterpart, and
   `(pull (boundary n).ι).map f`. Exact. I read Mathlib's `boundary`, the marked
   product definition, and the complete `pullObject` and `pull` constructions.
   The factor order is boundary ×_simplex X, canonically the node's pullback.
   An edge is marked exactly when its projection to X is marked.
6. The specified marked inverse over the boundary: `rBoundary` with source the
   Y boundary pullback and target the X boundary pullback. Exact; this is input,
   not a choice made by the conclusion.
7. The specified sharp mapping edge on the boundary: `hBoundary`, with
   `hBoundary₀` setting `δ 1` to `mapVertex (fBoundary ≫ rBoundary)` and
   `hBoundary₁` setting `δ 0` to `mapVertex (𝟙 _)`. Exact orientation: `δ 1`
   is the source, and composition `fBoundary ≫ rBoundary` means rBoundary fBoundary.
   I read `productLeft`, `mapSharp`, `sharpSimplex`, and `mapVertex`; this edge
   is a marked map X_boundary × (Δ[1])^sharp → X_boundary over the boundary.
8. Existence of a whole-simplex marked inverse map and sharp edge: the ordered
   existential `∃ (r : Y ⟶ X) (h : (mapSharp X X) _⦋1⦌)`. Exact; neither
   interior datum is required in a hypothesis.
9. The endpoints h : rf → id_X: the first two conjunctions use `δ 1 h =
   mapVertex (f ≫ r)` and `δ 0 h = mapVertex (𝟙 X)`. Exact. The node requests
   one such homotopy, not a second homotopy of fr to id_Y.
10. Exact restriction of r: `(pull (boundary n).ι).map r = rBoundary`. Exact;
    this is equality of marked maps in the boundary slice.
11. Exact restriction of the entire h: the last equation precomposes `h.left.val`
    with `pullback.snd ... ▷ Δ[1]` and equates it to `hBoundary.left.val`
    followed by `pullback.snd ...`. Exact, not an equality of homotopy classes.
    Both maps have domain X_boundary × Δ[1] and codomain X. The boundary
    projection to X is monic (a pullback of the boundary inclusion). Moreover,
    the boundary component is prescribed by the over-base condition, so this
    equation determines the restricted pullback-valued cylinder in every degree.
    The markedness and over-base witnesses are propositions, so their equality
    adds no choice or additional condition.

Dependency verdict: the relative marked-anodyne node's source module exports the
exact arbitrary-base slice, natural marking, pullback, and sharp mapping interfaces
used here. Its `relative_marked_anodyne_calculus` includes natural pullback marking
and the sharp core assertion. The enhanced-diagrams node explicitly defines the
coherent quasi-inverse convention used by `hf`; its recorded module supplies that
declaration even though its primary declaration is `coneCategory`. These are not
private copies or similarly named alternative notions. No dependency repair or new
definition is needed. All currently recorded proof-dependency modules are imported;
the same three unstated proof nodes noted by the worker remain without modules.

Edge cases: for n=1 the boundary contains both vertices but no interior edge,
so arbitrary prescribed vertical boundary homotopies are retained. For n>1 every
vertex is likewise in the boundary. n=0 is intentionally outside this lemma and
is treated separately in the HTT proof. Empty total spaces and empty fibers are
allowed; no nonemptiness instance is present. Degenerate edges remain marked by
the actual marked-set structure. The map f need not be injective or surjective
on simplices. No characteristic, field, ring, scheme, zero-object, or nonempty
index assumption is introduced. The arbitrary bound universe `u` covers all the
small simplicial sets in the node; their strict pullbacks and mapping simplices
stay in that universe. There is no auxiliary universe equality.

Independent searches (different wording from the worker):

- LeanSearch via `msearch.py`: “A fiberwise equivalence of cartesian fibrations
  extends a chosen retraction and natural homotopy from a simplex boundary”;
  eight hits about set-theoretic fiber equivalences, ordinary fibered categories,
  and Brown factorizations, none the prescribed simplicial boundary extension.
- LeanFinder via `msearch.py`: “Extend a specified boundary retraction and natural
  equivalence between cartesian fibrations across a simplex”; eight hits about
  pointed simplices, strict Segal objects, and extra degeneracies, none this lemma.
- Loogle via `msearch.py`: `SSet.boundary, CategoryTheory.Over`; zero hits.
- Grep via `msearch.py`: `simplex.*retract|boundary.*homotopy|relative.*inverse`
  in AlgebraicTopology; zero hits.
- Direct `rg` for `simplex.*(inverse|retract)|boundary.*(inverse|retract)|
  (inverse|retract).*boundary|cartesian_simplex_inverse_extension` across upstream
  `WeilConjectures`, Mathlib AlgebraicTopology, and shared `lean/Sheaf`: unrelated
  inverse constructions and the downstream marked-relative-model proof citation,
  not an existing declaration. In particular the downstream fiberwise weak
  equivalence clause is not this specified-boundary extension lemma.

Faults and changes: none in the Lean statement or node. I retained the correct
module and signature verbatim and appended only this review. The one postponed
theorem has the source/blueprint docstring and all eleven proof steps with their
dependency references; there are no new data definitions or helper sorries.
The node differs from the shared base only in `lean`, its `lean.statement` equals
the file signature verbatim, every universe and variable is bound, and all Lean
lines satisfy the 100-character convention. Compilation and delivery validation
are recorded below.

Validation: the independent `scompile.py Q92
lem-coef-cartesian-simplex-inverse-extension
lean/Sheaf/AlgebraicTopology/CartesianSimplexInverseExtension.lean` run passed
both the sandbox and library single-file checks (2.1 s and 2.0 s), without errors
or warnings. `deliver2.py ... --no-push` returned `OK (dry run)`: the complete
packet passes the server preflight and compiles. No theorem was proved in this
stage; the item's sole proof remains `sorry`.
