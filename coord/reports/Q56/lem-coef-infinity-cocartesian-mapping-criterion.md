## Worker report

`Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion` states
`SSet.Enhanced.infinity_cocartesian_mapping_criterion` with its sole theorem proof
`sorry`. Its three helpers construct the canonical triangle-roof presentation
of precomposition. No definition chooses data from a postponed theorem.

Source read: Lurie, Higher Topos Theory, Proposition the project server, printed pp. 131--132,
and its proof's strict representative square. The proposition is Cartesian;
reversing simplices gives the cocartesian criterion here. The current DAG
node's seven proof steps were read in full. The module docstring for the theorem
carries all seven steps, their dependency names, and the comparison with the
triangle presentation. Kerodon's triangle convention is the one already
recorded by the mapping-composition and spine nodes.

Each hypothesis and clause is rendered as follows.

- The fixed universe is `universe u`; `E B : SSet.{u}` and the two
  `Quasicategory` instances are exactly the two quasicategories in that universe.
- `p : E ⟶ B` and `_hp : InnerFibration p` are the stated inner fibration.
  There is no cocartesian-fibration assumption.
- `x y : E _⦋0⦌` are vertices. `s : Δ[1] ⟶ E` is the tested edge, with
  `_hsx` identifying its source (`δ 1`) and `_hsy` its target (`δ 0`).
  These endpoint equations express the edge's typing; they restrict no case.
- `IsCocartesianEdge p s` is the recorded initial outer-horn lifting condition,
  for every dimension at least two and with ordered edge `01` fixed to `s`.
- `∀ z : E _⦋0⦌` is the node's test at every target vertex.
- The point `u` is required to satisfy
  `(arrowMappingSpaceInclusion E x y).app _ u = diagramVertex s`.
  The arrow-space inclusion is monomorphic, so this determines `u` uniquely
  as precisely the displayed edge. It is not an arbitrary mapping-space point.
- The upper left corner is `cocartesianPrecompositionSource E x y z u`,
  the pullback of `spineRestriction E 2 ![x,y,z]` along `(u,id)`.
  Its second projection to `arrowMappingSpace E y z` is a trivial Kan
  fibration, by the recorded spine theorem and stability of boundary lifting
  under base change. Thus it is a canonical model of `Map_E(y,z)` carrying
  the entire composition triangle. The corresponding construction in `B`
  models `Map_B(p(y),p(z))`.
- The upper and lower horizontal maps `cocartesianPrecomposition` restrict
  those very triangles to edge `02`. Their roofs, whose other legs restrict
  to `12`, are precomposition by `s` and `p(s)`, respectively. This is exactly
  the defining triangle characterization in `MappingCompositionStatement`,
  with factors rearranged from `(12,01)` to the spine's `(01,12)`.
- The right corners are `arrowMappingSpace E x z` and
  `arrowMappingSpace B (p.app _ x) (p.app _ z)`. The right vertical map is the
  existing, explicitly constructed `arrowSpaceMap p x z`.
- The left vertical map `g` is fixed by the equation on
  `cocartesianPrecompositionInclusion` to postcompose whole triangles by `p`.
  That inclusion is monomorphic: the fixed-vertex inclusion is a pullback of
  the monomorphism from `Δ[0]` fixing the vertex tuple, and fixing edge `01`
  is a pullback along the monomorphism `(u,id)`. Consequently `g` is uniquely
  the canonical induced map, including every higher simplex. Existentially
  specifying it by this inclusion equation avoids choosing any fillers.
- `IsHomotopyPullbackSquare` uses the existing path-space pullback and its
  canonical constant-path comparison, tested by `IsWeakHomotopyEquivalence`.
  The long-edge restrictions commute strictly with postcomposition on whole
  triangles, so its commutativity witness supplies the prescribed coherence.
- The natural right-pinch comparisons identify each arrow space with the
  right-pinched mapping space stipulated by the node. The roofs identify the
  left corners and horizontal arrows with its coherent precomposition maps.
  This is a presentation of that square, not a square with an independently
  chosen commutation homotopy. Homotopy-pullback invariance under these natural
  equivalences gives precisely the node's path-pullback test.
- Neither the existential point nor the canonical map asserts another
  cocartesian lift. Both exist for any edge and any simplicial functor with
  its stated endpoints, independently of cocartesianness.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`,
  `mappingSpace`, `mappingSpaceMap`, `IsWeakHomotopyEquivalence`; the primitive
  Mathlib `SSet`, simplices and `Quasicategory` are used directly.
- `Sheaf.CategoryTheory.InfinityFibrations`: `IsCocartesianEdge`, using the
  actual `SSet.InnerFibration` class from Mathlib.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `MappingCompositionStatement`
  and `mapping_composition`, whose fixed triangle restriction characterization
  identifies the roof's horizontal map with canonical precomposition.
- `Sheaf.CategoryTheory.SimplicialCompositionSpine`: `multiarrowSpace`,
  `multiarrowInclusion`, `multiarrowEdge`, `spineRestriction`, `binaryArrowPair`,
  `arrowSpaceMap`, and `simplicial_composition_spine`. These already construct
  the canonical multiarrow and arrow maps; no private replacements are made.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, and `right_pinch_comparison`, read with their
  full degreewise formulas and naturality clause.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `IsHomotopyPullbackSquare` and
  `homotopyPullbackComparison`, read with the exact constant-path formula.

Two already landed nodes are added to `stmt_deps`, as allowed by brief-stage2
section 5: `def-coef-infinity-relative-cone` supplies the existing path-square
predicate; `lem-cbc-simplicial-composition-spine` supplies the existing canonical
triangle maps. No dependency node is modified, no new node is needed, and the
item's natural-language statement and proof remain unchanged. Available proof
modules are imported non-publicly for all the node's other proof dependencies.

Edge cases checked before the final formulation:

- Empty `E` has no tested edge; an empty target mapping space is allowed by
  the Kan, boundary-lifting and weak-equivalence conventions. No nonemptiness
  of any mapping space is assumed.
- The minimum horn is `Λ²₀`; the degree-zero boundary test remains present.
  The higher roof simplices fix the whole first edge, not just its endpoints.
- For `p = id`, its canonical square has identity vertical maps and passes the
  test for every edge, as does the relative horn criterion.
- For an identity edge, the triangle roof represents the identity map up to
  its canonical unit homotopy, and the square passes the test.
- For `B = Δ[0]`, the criterion reduces to precomposition being an equivalence
  for every target, hence to `s` being an equivalence. For `N([1])` and its
  nonidentity edge, the test at `z = 0` fails (`empty → point`), agreeing with
  its failed outer horn. Ordinary category nerves give the usual cocartesian
  Hom pullback criterion.
- Repeated endpoints and equal vertices are retained; none of the helper
  constructions uses distinctness. There is one universe and no size equality
  or inhabitedness added.

Searches actually run in this repair:

- `msearch.py ... leanfinder "An edge of an inner fibration of quasicategories
  is cocartesian exactly when its canonical mapping space squares are homotopy
  pullbacks"`: eight hits, consisting of ordinary category
  `IsStronglyCocartesian`/`IsCocartesian` and Quillen fibration declarations;
  none states the quasicategorical mapping criterion.
- `msearch.py ... loogle '"IsCocartesian", "Quasicategory"'`: zero hits.
- `msearch.py ... grep 'cocartesian|coCartesian|mapping.*pullback|pullback.*mapping'
  AlgebraicTopology/Quasicategory`: zero hits.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, for the node id and proposed full names:
  only existing proof-docstring references to this item, no existing theorem.
- Concept searches in project `lean/Sheaf/CategoryTheory` for coslices,
  mapping composition, precomposition and triangle restrictions found the
  landed `SimplicialCompositionSpine` interface. Its entire helper definitions
  and theorem signature were read and reused.
- `rg` in Mathlib for the final helper/theorem names found no declarations.
  Mathlib's ordinary cocartesian declarations and its inner-fibration
  definition were read; neither replaces this theorem.

Repairs of the earlier sandbox attempt: removed the definition choosing a
composition representative from mere existential theorem data; removed the
incorrect strict-naturality requirement on independently chosen representatives;
reused the existing spine and arrow maps to give the canonical coherent roof
square. The old node copy was refreshed from the current shared node, preserving
its `lean_audit`, and only the allowed `lean` and added landed `stmt_deps` fields
change. The UTC date is obtained from `date -u +%F`. The stale second-reading
text covered the old file and has been removed; the assigned second reader must
read this final version.

No `STATEMENT-DISPUTED` flag or source/node correction is needed: the issue was
in the earlier Lean presentation, and the node explicitly retains the coherent
square by a natural roof in proof steps 6--7. `scompile.py` compiled the final
module with its proof imports cleanly; its sole postponed theorem is the item.

Completion check on 2026-10-17: re-read the current node, every statement
dependency record and declaration, and HTT Proposition the project server and its strict
representative argument on printed pp. 131--132. The triangle roof construction
and theorem remain unchanged. Repeated the LeanFinder criterion query, Loogle
`"IsCocartesian", "Quasicategory"`, and the Mathlib quasicategory grep: eight
ordinary-category or Quillen-fibration hits, zero hits, and zero hits, respectively.
The searches in upstream and project sources found only proof-docstring citations
of this item. `scompile.py` compiled both wrapper and library-path versions
cleanly (1.8 and 1.6 seconds). Updated only the UTC Lean-record date.

The inherited second-reading section was removed for a fresh independent reading
by the assigned second reader; this worker has not supplied a second reading.

## Second reading by Q56

Independent second reading of the final module, the shared node (all seven proof
steps), its five statement dependencies, and their declaration sources. Read HTT
Proposition the project server and its full proof on printed pp. 131--132 in
`scratchpad/HTT.txt`, and checked the same proposition in the
[online source](https://people.math.harvard.edu/~lurie/papers/HTT.pdf).
The source assumes an inner fibration of quasicategories, without other
cocartesian lifts. Its warning that a square of homotopy classes is insufficient
is respected by the fixed triangle presentation here. The proposition is
Cartesian; opposite reversal gives exactly the node's outgoing mapping square.
There is no Stacks source for this item. No statement correction, new node or
dependency-module repair is present or needed.

Object/hypothesis/conclusion checklist, written from the node and checked against
Lean:

1. Two quasicategories in one fixed universe: `E B : SSet.{u}` with
   `[Quasicategory E] [Quasicategory B]`. Verdict: exact; `u` is declared.
2. Inner fibration between them: `p : E ⟶ B`, `_hp : InnerFibration p`.
   Read Mathlib's `InnerFibration` and the recorded `InfinityFibrations` module;
   no cocartesian-fibration or existence-of-lifts assumption is added. Exact.
3. Vertices and a typed edge `s : x → y`: `x y : E _⦋0⦌`, `s : Δ[1] ⟶ E`,
   `_hsx : E.δ 1 (SSet.yonedaEquiv s) = x` and the corresponding `δ 0 = y`.
   These are the source and target equations, not extra geometric hypotheses.
   Exact, including repeated endpoints and degenerate edges.
4. Horn-cocartesian iff the mapping-square test: `IsCocartesianEdge p s ↔ ...`.
   Opened the definition: it tests every `n ≥ 2` initial horn, fixes the ordered
   edge `01`, and requires a filler over the given base simplex. This is precisely
   the node's dependency, not an ordinary-category cocartesian predicate. Exact.
5. Every target vertex, in the right order: `∀ z : E _⦋0⦌` occurs after the
   equivalence. The subsequent existential `u` is constrained by
   `(arrowMappingSpaceInclusion E x y).app _ u = diagramVertex s`. The inclusion
   is the pullback of the mono fixing the endpoints; hence this specifies the
   unique point for the given edge, not a freely chosen edge for each test. Exact.
6. Upper left mapping space: `cocartesianPrecompositionSource E x y z u` is a
   concrete pullback of `spineRestriction E 2 ![x,y,z]` along `(u,id)`, using the
   landed `binaryArrowPair`. Its second projection to `arrowMappingSpace E y z`
   is trivial Kan, since the spine theorem lifts every boundary and base change
   preserves lifts. The target is Kan by `right_pinch_comparison`; the source is
   consequently Kan too, including the empty case. It is the canonical triangle
   model of the intended corner. The bottom left is the identical construction
   in `B` for `(arrowSpaceMap p x y).app _ u`. Exact up to the specified natural
   equivalences, as the node permits in proof steps 6--7.
7. Horizontal maps: both `cocartesianPrecomposition` restrict the retained
   triangle to `02` via `SimplexCategory.δ 1`. The second projections restrict to
   `12`, so their roofs represent precomposition by the fixed `01` edge. Opened
   `MappingCompositionStatement`, `multiarrowRestriction`, `multiarrowEdge`,
   `spineRestriction` and `binaryArrowPair`: the first composition interface uses
   order `(12,01)` while the spine uses `(01,12)`; the helper pairs them in the
   spine's order. Exact; there is no reversed composition.
8. Right corners and vertical map: `arrowMappingSpace E x z`,
   `arrowMappingSpace B (p.app _ x) (p.app _ z)` and `arrowSpaceMap p x z`.
   The latter's full pullback formula postcomposes by `p`. Opened
   `arrowMappingSpace`, `arrowMappingSpaceInclusion` and the degreewise prism
   formula/naturality of `right_pinch_comparison`: these are the recorded natural
   arrow models of the stipulated right-pinched mapping spaces. Exact.
9. Left vertical map/coherence: the existential `g` must satisfy the displayed
   equation after `cocartesianPrecompositionInclusion`. This inclusion is mono:
   `multiarrowInclusion` is a pullback of the mono from `Δ[0]` fixing the vertex
   tuple, and the first roof projection is a pullback of the mono `(u,id)`.
   Therefore the equation determines `g` on all simplices as postcomposition of
   the whole triangle by `p`. Such a map exists for every `p` and typed edge,
   independently of cocartesianness. Restriction to `02` then commutes strictly.
   This retains the natural coherent square, rather than introducing an arbitrary
   homotopy of its arrows. Exact.
10. Homotopy-pullback clause: `IsHomotopyPullbackSquare` of these four maps.
    Opened that predicate and `homotopyPullbackComparison`: it asks for the
    weak-equivalence property of the constant-path comparison into the recorded
    path-space pullback. Equality proofs are propositions, so its existential
    commutativity proof supplies no independently variable homotopy. Natural
    right-pinch comparisons and the triangle roofs identify this strict diagram
    with the node's coherent precomposition square. Exact.
11. No other cocartesian lifts: neither `u` nor `g` asks for any; the hypotheses
    and conclusion have no such clause. All quantifiers are bound. Exact.

Edge cases: empty `E` has no edge to instantiate and empty `B` permits no map
from a nonempty `E`; there is no accidental nonemptiness assumption. Empty arrow
spaces and empty roof spaces are allowed. The boundary degree `m = 0` in the
spine theorem is retained and corresponds to the horn dimension `n = 2`; there
is no missing zero-dimensional test. At `p = id` every edge passes (identity
verticals); at an identity edge the unit roofs pass for every inner fibration.
At `B = Δ[0]` the criterion detects equivalence edges. For the nonidentity edge
of `N([1])`, testing `z = 0` gives an empty upper left and a singleton upper
right, and fails, as does its prescribed initial horn. Ordinary category nerves
recover the Hom pullback test. Repeated vertices and all universe levels are
retained. Ring characteristic, zero objects and schemes are not data of this
node; no restrictions on them enter implicitly.

Independent searches, with different wording from the worker:

- `msearch.py ... leanfinder 'An inner fibration edge is cocartesian if its
  induced squares of morphism spaces are homotopy Cartesian'`: eight hits,
  ordinary `CategoryTheory.Functor.IsCocartesian` / `IsStronglyCocartesian`.
- `msearch.py ... loogle '"IsStronglyCocartesian"'`: twelve ordinary-category
  declarations. Opened Mathlib `FiberedCategory/Cocartesian.lean`, including
  both class signatures and their Hom-set universal properties. None gives this
  quasicategory mapping-space theorem.
- `msearch.py ... grep 'cartesian|homotopy.*pullback|morphism.*space'
  AlgebraicTopology/Quasicategory`: one hit, the future-work cartesian-closed
  comment in `StrictBicategory.lean`; no theorem match.
- `rg -i` in project `lean/Sheaf`, upstream `WeilConjectures`, and Mathlib's
  `AlgebraicTopology`, for cocartesian/mapping permutations, precomposition
  source/triangle, the helper names and the theorem name: only references in
  proof docstrings and unrelated precomposition declarations, no duplicate.
  Opened the existing spine/triangle definitions before accepting the three
  helpers as restrictions of the owning construction rather than new notions.

Mismatch and repair: the proof dependency
`lem-coef-infinity-pinch-comparison` was available transitively but had no direct
proof import, contrary to stage-2 import convention. Added the non-public import
`Sheaf.CategoryTheory.RightPinchComparison`. No mathematical signature or
construction was changed. The three helper definitions contain concrete data,
not choices from mere existence theorems; the sole postponed theorem has the
item's matching DAG statement and complete seven-step source proof docstring.
Module/declaration source-blueprint docstrings and the 100-column limit pass.
The node's `lean.statement` was checked verbatim against the theorem signature.
`scompile.py` compiled both sandbox and library-path versions cleanly before the
import repair; the required final compile and delivery preflight follow below.

Final validation: after the import repair, `scompile.py` compiled the sandbox
and library-path module cleanly (1.3 s and 1.4 s). `deliver2.py --no-push`
returned `OK (dry run)` at `0c986f8f83`: server preflight and compilation pass.
