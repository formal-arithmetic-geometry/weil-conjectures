## Worker report

The module `Sheaf.CategoryTheory.LinearCofinalConeExtension` defines the particular
subcomplex `SSet.Enhanced.linearCofinalUnion` and states
`SSet.Enhanced.exists_linearCofinalConeExtension`, with its sole theorem proof `sorry`.
The node's statement and dependency lists are unchanged. No definition contains `sorry`.
All writes are in this item's sandbox, and compilation used only `scompile.py`.

The statement is rendered hypothesis by hypothesis and clause by clause as follows:

- A small linearly ordered set is `(A₀ : Type u) [LinearOrder A₀]`, with the universe
  explicitly declared. Its subset is `(B : Set A₀)`.
- Cofinality is exactly `hcof : ∀ a : A₀, ∃ b : A₀, b ∈ B ∧ a ≤ b`.
- The adjoined new greatest element is Mathlib's `WithTop A₀`: every old element is
  included by coercion, and the distinct new element is `⊤`. This adds a new element
  even if the original order already has a greatest element.
- `N(A)` is `CategoryTheory.nerve (WithTop A₀)`, using the existing preorder category.
- The first full subcomplex in `linearCofinalUnion` selects vertices represented by
  old elements. The second selects vertices equal to `⊤` or represented by members
  of `B`. Since these are full ordered subcategories, their full nerve subcomplexes
  are precisely `N(A₀)` and `N(B ∪ {∞})`. Their intersection is `N(B)`.
- The outer `⊔` forms the union degree by degree. It does not take the full subcomplex
  on the union of vertex sets (which would incorrectly give the entire nerve).
  `fullSubcomplex` uses the vertices of each whole simplex, so higher coherent
  compatibility data are retained.
- An arbitrary quasicategory is `(C : SSet.{u}) [Quasicategory C]`, using the dependency's
  existing simplicial-set and inner-horn conventions. No category, filteredness,
  Kan condition, or colimit-existence assumption is imposed on `C`.
- The supplied map is `h : (linearCofinalUnion A₀ B : SSet) ⟶ C`.
- The conclusion quantifies `barh : CategoryTheory.nerve (WithTop A₀) ⟶ C` and requires
  `(linearCofinalUnion A₀ B).ι ≫ barh = h`, which is exact equality on the union.
- There is no `Nonempty A₀` or `Nonempty B` assumption, so the empty case is included.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` (node
  `def-cbc-enhanced-diagrams-cones`): read the full node, declarations and docstrings.
  The recorded `SSet.Enhanced.coneCategory` is the coherent comma construction;
  this particular assertion instead uses its foundational `SSet`, `Quasicategory`,
  `CategoryTheory.nerve` and `SSet.Enhanced.fullSubcomplex` interfaces. The imported
  module explicitly reuses the Mathlib primitives, and the union directly calls
  the recorded dependency's `fullSubcomplex`, without a private replacement.
- Mathlib `CategoryTheory.nerve` has simplices `ComposableArrows C n` (functors from
  the finite ordinal) and restriction maps. Read its definition and docstring in
  `AlgebraicTopology/SimplicialSet/Nerve.lean`.
- Mathlib `SSet.Quasicategory` is precisely the inner-horn filling property. Read
  its full signature and docstring in `AlgebraicTopology/Quasicategory/Basic.lean`.
- Mathlib `WithTop`, its order in `Order/WithBot.lean`, `SSet.Subcomplex`, its coercion
  and inclusion `ι` in `AlgebraicTopology/SimplicialSet/Subcomplex.lean` supply the
  remaining standard constructions. There are no proof dependencies to import.

Edge cases checked by inspecting the definitions:

- For `A₀ = B = ∅`, `WithTop A₀` has only its new top. The second full subcomplex is
  the whole nerve, including the vertex; thus the assertion just retains `h`.
- If `A₀` is nonempty and `B` empty, `hcof` is false: take any `a`.
- If `B = Set.univ`, the second subcomplex is already the entire nerve.
- For an order with an existing maximum, `WithTop` still adjoins a distinct maximum;
  for a singleton with its cofinal singleton subset the union is the entire edge.
- No well-order, countability, cardinal regularity, or nonemptiness is assumed.
- If `C` is empty, the hypothesis map cannot exist, since the union contains the
  new top vertex. The statement does not incorrectly force `C` to be inhabited.

Source check: opened [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf), Lemma
the project server, printed p. 444, and the extension applications in the project server, pp. 445--446.
The lemma gives a monomorphic categorical equivalence; lifting against the terminal
map of a fibrant quasicategory gives exact extension. The module docstring includes
this proof plan, including the separate empty case. The node's `proof` list is empty.
No statement correction, dependency repair, new independent notion, or disputed
statement was needed. The helper names the specific union already specified in this
node and is listed in `lean.declarations` under the authorized owning-node helper rule.

Searches for an existing statement (all via the prescribed wrapper or read-only `rg`):

- `msearch.py ... leanfinder "Extend a simplicial map from a linear order and a cone
  on a cofinal subset to its full cone in a quasicategory"`: eight hits, concerning
  strict Segal coskeletal extension and finite horn colimits. Those impose strict
  Segal hypotheses or concern individual finite horns, not this arbitrary union.
- `msearch.py ... loogle 'SSet.Quasicategory, "extension"'`: zero hits.
- `msearch.py ... grep 'cofinal|anodyne|cone' AlgebraicTopology/Quasicategory`: zero hits.
- `msearch.py ... leansearch "Extending a coherent cone on a cofinal subset of a
  linearly ordered set into any quasicategory"`: eight hits, ordinary-category
  `Cone.extend`, `Cocone.extend`, `Functor.Final.extendCocone`, and order cofinality
  constructors. These do not state extension of arbitrary coherent simplicial maps.
- `rg` for `linearCofinalUnion|exists_linearCofinalConeExtension|cofinal.*[Cc]one|[Cc]one.*cofinal`
  in `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`: only two
  unrelated ordinary derived/cohomological cone docstrings in `lean/Sheaf/`.
- `rg` for the exact item ID in upstream `WeilConjectures/`: no hits.
- `rg` for `cofinal|Cofinal|linear.*[Cc]one` in Mathlib's simplicial-set anodyne modules
  and nerve module: no hits.
- Inspected Mathlib's nerve, quasicategory and subcomplex interfaces directly; these
  provide primitives, not the extension assertion.

Validation: final `scompile.py Q21 lem-coef-infinity-linear-cofinal-cone-extension
<module>` compiled both the sandbox and library module successfully, approximately
1.2 seconds each, with no errors or warnings. `set_option autoImplicit false` applies
throughout. The node's `lean.statement` was extracted verbatim from the final file.
The UTC record date follows the required `date -u +%F` command (2026-10-16), even
though the environment's local calendar date is 2026-10-17.


## Second reading by Q21

I independently read the current node (including its ten proof steps), the whole delivered
module, the full statement and recorded declarations of
`def-cbc-enhanced-diagrams-cones`, and the actual definitions used below. I also opened
HTT Lemma the project server and the two extension applications in the project server at
https://www.math.ias.edu/~lurie/papers/HTT.pdf (printed pp. 444--446). The lemma's linear
order and cofinality assumptions are exactly the node's; accessibility and cardinal
hypotheses belonging to the following lemma do not apply to this extension assertion.
There is no matching Stacks source. No source-based statement correction is needed.

Object/hypothesis/conclusion checklist (each verdict is exact):

1. The small underlying linearly ordered set is `(A₀ : Type u) [LinearOrder A₀]`.
   No well-order or nonemptiness is assumed. This is the order in the node, with its
   ordinary thin category used only to take the nerve.
2. The subset is `(B : Set A₀)`, with no independent or additional order data.
3. Cofinality is `hcof : ∀ a : A₀, ∃ b : A₀, b ∈ B ∧ a ≤ b`. In particular it is
   weak cofinality including equality, rather than strict unboundedness.
4. The order with one new greatest element is `WithTop A₀`, old elements are coercions,
   and the extra point is `⊤`. I read the WithTop/WithBot order implementation: even
   an existing greatest old element is strictly below this newly adjoined point.
5. The ambient simplicial set is `CategoryTheory.nerve (WithTop A₀)`. The Mathlib nerve
   is `ComposableArrows` with operators given by precomposition, exactly the finite
   weakly increasing lists specified by the dependency and the node.
6. In `linearCofinalUnion`, the first `fullSubcomplex` imposes that each vertex equals
   an old element, hence gives the embedded `N(A₀)`. The predicate `s.obj 0` refers to
   the sole object of a vertex, not merely the initial vertex of a higher simplex:
   `fullSubcomplex` tests this predicate after restriction to EVERY vertex.
7. The second `fullSubcomplex` tests `s.obj 0 = ⊤ ∨ ∃ b, b ∈ B ∧ s.obj 0 = b`.
   It is precisely the embedded `N(B ∪ {∞})`, and its intersection with the first
   piece is `N(B)`.
8. The outer `⊔` is the lattice supremum of subfunctors: the degreewise union of the
   two pieces. This retains exactly the node's union, including all degeneracies;
   it does not add simplices mixing vertices from the two pieces.
9. The target is `(C : SSet.{u}) [Quasicategory C]`. Mathlib's class requires fillers
   for all inner horns, exactly as in the dependency. No filteredness, existence of
   colimits, Kan condition, or ordinary-category structure is assumed.
10. The initial datum is `(h : (linearCofinalUnion A₀ B : SSet) ⟶ C)`, an arbitrary
    simplicial map from that union, with all its coherent higher simplex data.
11. The conclusion is `∃ (barh : CategoryTheory.nerve (WithTop A₀) ⟶ C), ...`.
    Its quantifier follows all the data and hypotheses, and supplies an actual map.
12. The equation `(linearCofinalUnion A₀ B).ι ≫ barh = h` is equality of natural
    transformations, hence EXACT restriction to every simplex of the given union.
    No homotopy weakening, uniqueness assertion, or extra conclusion is present.

Dependency/interface inspection: the dependency's recorded `lean.declarations` includes
`SSet.Enhanced.fullSubcomplex`, whose concrete data I read in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`. It checks all vertex restrictions; it is
neither a generated span nor a strict ordinary category. Its public imports expose the
existing Mathlib `SSet`, `Quasicategory`, and `CategoryTheory.nerve` implementations.
I read Mathlib `AlgebraicTopology/Quasicategory/Basic.lean` (class and horn filling),
`AlgebraicTopology/SimplicialSet/Nerve.lean` (nerve and nerve vertex equivalence), and
`AlgebraicTopology/SimplicialSet/Subcomplex.lean` (subfunctor, underlying simplicial set,
and canonical inclusion). The arbitrary canonical inclusion required by the node is
exactly this `ι`; no arbitrary map or choice replaces it. The helper is a construction
of the particular union already introduced by this node, with real data, listed in
`lean.declarations`; it introduces no independent definition node. There are no new
nodes or dependency modules to review under H12/H13.

Edge cases: when `A₀ = B = ∅`, the second piece contains the only vertex and every
simplex of the one-point nerve, so the given map is already the desired map. If `B`
is empty and `A₀` inhabited, `hcof` fails. If `B = Set.univ`, the second piece is the
whole nerve. For a singleton old order, cofinality forces its point into `B`, so the
whole edge to the NEW top is present. For two points `a < b` and `B = {b}`, the union
contains the two edges `a → b → ∞`, and the missing triangle is an inner-horn filler;
this tests the orientation and the degreewise-union interpretation. At simplicial
degree zero all old vertices and the new top are present, so no new object of `C`
needs to be chosen. An empty `C` admits no `h`; the assertion stays valid. Zero objects,
characteristic and schemes play no role. The explicit universe `u` is arbitrary and
unbound universes/variables are absent (`autoImplicit false`). Both simplicial sets
are small in the chosen common universe, as in the dependency's size convention; no
finite/countable size restriction or equality of site universes is introduced.

Independent one-definition searches (different wording from the first reader):

- `msearch.py ... leanfinder "A map from the union of a total order nerve and a terminal
  cone on a cofinal suborder extends into an inner Kan simplicial set"`: eight hits.
  They concern simplicial thickening, the nerve functor, strict-Segal/coskeletal right
  extension, and `SSet.horn.isColimit`. Their inspected types require strict Segal
  objects or describe individual horn gluing; none is this assertion.
- `msearch.py ... loogle '"innerAnodyne", "nerve"'`: zero hits.
- `msearch.py ... leansearch "Every homotopy coherent cocone on an unbounded suborder
  extends along the nerve of the total order"`: eight hits, ordinary-category
  `Cocone.extend`, `Functor.Final.extendCocone` and their properties. Their codomains
  have an ordinary `Category` structure and do not give this quasicategory statement.
- Read-only `rg` for `unbounded|cofinal|Cofinal|terminal.*cone|cone.*terminal` in Mathlib's
  quasicategory, inner-anodyne and nerve sources, and upstream/project CategoryTheory:
  no exact match; project hits concern other coherent cone or ordinary/derived
  colimit results. Exact helper/theorem names and cofinal-cone variants across all
  upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  gave only unrelated derived/etale-limit docstrings. A separate search for
  `fullSubcomplex`, spanned subcomplexes and vertex subcomplexes found only the
  dependency's own full-subcomplex construction among relevant simplicial notions.

Mismatches found and repaired:

- H8: the original theorem docstring summarized a categorical-equivalence/Joyal
  argument, whereas the current node carries ten explicit inner-horn proof steps.
  I replaced only the proof-plan portion with those ten steps, including the exact
  horn intersection, disjointness, finite-support limit and total graph-valued
  recursion arguments. The mathematical signature and real union data were right
  and remain unchanged.
- Import convention: the current proof dependencies also include
  `lem-weil-pbc-transfinite-recursion` and `lem-weil-pbc-well-ordering-theorem`, both
  Mathlib leaves. I read their nodes and their exact bindings `WellFoundedLT.fix`,
  `WellFoundedLT.fix_eq` in `Mathlib.Order.RelClasses`, and `exists_wellFoundedLT` in
  `Mathlib.SetTheory.Cardinal.Order`, and added their ordinary proof-only imports.
- The retained Worker report's sentences saying the node has an empty proof and no
  proof dependencies are stale; the current base and sandbox BOTH have ten steps
  and these two Mathlib leaves. This section supersedes those sentences. All node
  fields except the delivered `lean` record already match the shared base exactly.

No H3 signature mismatch, hollow definition, proof, unbound variable, statement
correction, duplicated notion, or disputed mathematical statement remains. The only
postponed proof is the named theorem's `sorry`, matching this node. Module and both
declarations carry the source and blueprint marker. The recorded `lean.statement`
was independently checked verbatim against the unchanged theorem signature.
