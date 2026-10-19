## Worker report

`Sheaf.CategoryTheory.MarkedMappingSimplexDescent` states
`SSet.Marked.Over.marked_mapping_simplex_descent`, with its entire proof `sorry`.
The original natural-language node is unchanged; only its `lean` field changes.
The module supplies the canonical maps needed to state the result:
`unmarkMap`, `funOverPre`, `functorRestriction`, `enlargeObject`, and `enlargeHom`.
Their data are explicit constructions, with only the structural equations proved
inside their definitions. They are helpers of this node, listed in
`lean.declarations`; no independent notion or additional postponed theorem is
introduced.

The correspondence with every hypothesis and clause of the node is as follows.

- Small simplicial sets and the fixed small quasicategory are
  `(S : SSet.{u}) [Quasicategory S]`. All universes and variables are explicitly
  bound, with `autoImplicit false`.
- A marked simplicial set over `S` is the dependency's `SSet.Marked.Over S`,
  namely the existing slice over `Marked.sharp S`. Its morphisms preserve
  markings and commute with the map to `S`.
- A cocartesian fibration with precisely its cocartesian edges marked is
  `IsNaturallyFibrant true Z`; `true` selects the cocartesian case. This includes
  inner fibrancy, the edge-lift condition, and the exact marking equality.
- The specified simplicial set `F_S(U,Z)` is the dependency's
  `cartesianFunctors U Z`. This is the full subcomplex of `funOver U Z` selected
  by `PreservesMarkings U Z`. A simplex of `funOver` is a map
  `U × Δ[k] → Z` over `S`: both source and target markings have first been
  replaced by their degenerate markings. The full-subcomplex predicate tests
  the restrictions at every parameter vertex. Thus exactly the source's marked
  edges must be preserved at each vertex, and all higher transformations remain.
  Parameter edges are not required to be equivalences.
- The unconditional assertion that these are quasicategories for every marked
  source is the first conjunct
  `∀ (U Z : Over S), IsNaturallyFibrant true Z → Quasicategory (cartesianFunctors U Z)`.
  No fibrancy of `U` is assumed.
- The map in the descent assertion is `(X Y : Over S) (f : X ⟶ Y)`, without
  any injectivity, fibrancy, or cofibration hypothesis.
- The complete simplex-local hypothesis is
  `∀ (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ S), weak true ((pull σ).map f)`.
  It includes `n = 0`, all degenerate simplices, and all simplex maps.
  The dependency's `pull` forms the actual degreewise pullback and marks
  precisely those edges whose source-space projection is marked. Its coordinate
  order is `Δ[n] ×_S X`, canonically the same marked pullback as `X ×_S Δ[n]`.
- The first conclusion is `weak true f`, using exactly the relative cocartesian
  weak-equivalence predicate from the dependency, tested on sharp mapping spaces
  into all naturally marked cocartesian fibrations.
- For every such `Z`, the second conclusion is
  `Enhanced.IsFunctorEquivalence (functorRestriction (Z := Z) f)`.
  This is the dependency's coherent quasi-inverse criterion for the whole functor
  simplicial sets, including both natural inverse equivalences.
- The comparison is the specific precomposition map. `unmarkMap f` keeps the
  underlying simplicial map and base equation. `funOverPre` sends a parameterized
  map `a` to `(f × id) ≫ a`. `functorRestriction` factors that map through the
  existing full subcomplex; its marking proof uses `f.left.property` and the
  original vertex's `PreservesMarkings` proof. No arbitrary map is substituted.
- Universe relativity uses independent `u v` and the actual degreewise lift to
  `max u v`. `enlargeObject` and `enlargeHom` use the existing `Marked.enlargeMap`
  and retain the same base equation over `SSet.uliftFunctor.{v,u}.obj S`.
  The last two conjuncts assert `weak true (enlargeHom.{u,v} f)` and, for every
  naturally marked test object over this lifted base, the quasicategory property
  for both lifted-source mapping objects and the equivalence of their specified
  precomposition map. The theorem is uniform in `u`, so the initial mapping
  assertion also applies to arbitrary objects in every enlarged universe.
- No finiteness assumption on `S`, its simplex category, the sources, or the set
  of cells occurs in the signature.

The statement dependencies were read with their full signatures and docstrings:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded declaration
  `SSet.Enhanced.coneCategory`: its shared `fullSubcomplex`,
  `IsFunctorEquivalence`, `AreNaturallyEquivalent`, and `IsEquivalenceEdge`
  provide the full-subcategory and equivalence conventions used here.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`, recorded declaration
  `SSet.Marked.Over.marked_relative_cartesian_model`: its actual definitions
  `Over`, `unmark`, `funOver`, `PreservesMarkings`, `cartesianFunctors`,
  `IsNaturallyFibrant`, `weak`, `pull`, and `productMapLeft` are used directly.
  Its model theorem includes both cartesian and cocartesian structures; no
  model structure is assumed as a new hypothesis of this item.

The already stated proof-dependency modules are imported without `public`:
`RelativeMarkedAnodyneCalculus`, `ModelInfinityDerivedAdjunction`,
`MarkedCoanodyne`, `ModelCofibrantColimitComparison`,
`MarkedAnodyneLiftingCalculus`, `JoyalModelStructure`,
`JoyalQuasicategoryCharacterizations`, and `PointwiseEquivalences`.
The Mathlib leaf `lem-coef-infinity-monomorphism-boundary-cells` is represented
by `SSet.relativeCellComplexOfMono` in `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`,
which is also imported. The proof-only node
`lem-coef-relative-marked-anodyne-replacement` currently has no Lean record or
Mathlib match, so no module can yet be imported for it. It is retained in the
node's proof dependencies and in step 6 of the theorem's proof docstring; it
is not required to define any object in this stage-2 signature.

Edge cases were checked mathematically against the definitions: `n = 0` is
included; the empty base has no simplex maps and forces empty total spaces;
empty marked sources are allowed; degenerate markings and all-edge markings
use the same full-subcomplex construction; identity maps give ordinary
precomposition; arbitrary noninjective and nonfibrant maps are included.
For `S = Δ[0]`, the non-equivalence `∅ → Δ[0]` fails the local test already in
degree zero, so the hypothesis is not vacuous. The universe lift permits
`v = 0` and `v = u`, as well as strict enlargement, and test targets in the
larger universe are universally quantified. There is no empty or finite index
assumption to remove in the skeletal proof.

Searches repeated during completion (in addition to the earlier attempt's
record in `searches.jsonl`):

- `msearch.py ... leanfinder "Equivalences of relative marked mapping quasicategories can be checked after pullback to every simplex of the base"`:
  eight hits on ordinary horn filling, `SSet.Quasicategory`, and simplicial
  relative morphisms; no marked descent theorem.
- `msearch.py ... leansearch "A map of marked simplicial sets is a cocartesian equivalence if its pullback over every simplex is a cocartesian equivalence"`:
  eight hits on ordinary category cocartesian arrows and the Kan-Quillen
  cofibration criterion; none states the relative marked result.
- `msearch.py ... loogle '"CartesianEquivalence"'`: zero hits.
- `msearch.py ... grep '[Cc]artesianEquivalence|[Cc]artesian_equivalence|marked.*descent|descent.*marked'`:
  zero Mathlib hits.
- `rg` in the upstream `WeilConjectures`, the project's `lean/Sheaf`, Mathlib,
  and `dag/lean_names_upstream.json` for `marked_mapping_simplex_descent`,
  `functorRestriction`, `funOverPre`, `unmarkMap`, `enlargeObject`, and `enlargeHom`:
  no existing declaration. Searching the upstream source for the node id also
  gives no match. The existing `Marked.enlarge`/`enlargeMap` were found and
  reused instead of rebuilding the marked universe lift.

The sandbox's local HTT text was read at Remark the project server (flat mapping objects
are quasicategories for arbitrary marked sources), Proposition the project server and its
proof (the equivalence on whole flat mapping objects), Remark the project server (marked
anodyne restriction), and Proposition the project server with its proof (skeletal simplex
locality). As the node explicitly says, the marked descent formulation is
agent-formulated from these results, rather than a verbatim restatement of
Proposition the project server. The docstring preserves the node's ten-step proof and all
its cited dependency ids.

The earlier attempt's `statement_change` and its paraphrased natural statement
were removed: the original node already explicitly contains the quasicategory
hypothesis, mapping-quasicategory conclusion, and universe enlargement clause.
There is no statement correction or statement dispute in this delivery.

Validation: the module compiles cleanly using the prescribed `scompile.py`,
with the original 60-second per-file limit. The only postponed proof is the
named theorem `SSet.Marked.Over.marked_mapping_simplex_descent`.

## Second reading by Q110

I independently opened the node record, its source text in the supplied HTT extract, the two
statement dependencies, and `MarkedMappingSimplexDescent.lean`. The item-by-item rendering is:

- The fixed base is the small simplicial set/quasicategory `S : SSet.{u}` with
  `[Quasicategory S]` (the node's fixed small quasicategory).
- A marked simplicial set over `S` is `X : Over S`, where the dependency declaration
  `SSet.Marked.Over` is the slice over `sharp S`; a map over `S` is `f : X ⟶ Y`.
- A cocartesian fibration marked by exactly its cocartesian edges is rendered by
  `IsNaturallyFibrant true Z`. The Boolean `true` is the dependency's cocartesian case,
  including inner fibrancy, cocartesian lifts, and the marking iff condition.
- The source mapping object `F_S(U,Z)` is rendered by
  `cartesianFunctors U Z`. Its vertices are the `PreservesMarkings U Z` full subcomplex of
  `funOver U Z`, and its higher simplices are retained by `Enhanced.fullSubcomplex`; thus
  the parameter edges are unrestricted and all transformations over `S` remain.
- The first conclusion, for every marked source `U` and naturally marked cocartesian target
  `Z`, is exactly
  `∀ U Z, IsNaturallyFibrant true Z → Quasicategory (cartesianFunctors U Z)`.
  No fibrancy of `U` is present.
- The descent map is `f : X ⟶ Y` with no injectivity, fibrancy, cofibration, or finiteness
  assumption. The local hypothesis is exactly
  `∀ n : ℕ, ∀ σ : (Δ[n] : SSet.{u}) ⟶ S, weak true ((pull σ).map f)`.
  Thus `n = 0`, degenerate simplices, and every simplex map are included.
- The first descent conclusion is `weak true f`, the dependency's relative cocartesian
  weak-equivalence predicate.
- For every naturally marked cocartesian `Z : Over S`, the whole mapping-quasicategory
  conclusion is exactly
  `Enhanced.IsFunctorEquivalence (functorRestriction (Z := Z) f)`.
  `functorRestriction` is the explicit precomposition induced by `unmarkMap` and
  `funOverPre`, followed by the existing full-subcomplex lift; it is not an arbitrary map.
- The universe-relative clause is rendered explicitly by `enlargeObject` and `enlargeHom`
  using the existing `Marked.enlargeMap`: it asserts `weak true (enlargeHom f)` and,
  for every naturally marked target over `SSet.uliftFunctor.{v,u}.obj S`, quasicategory
  properties for both enlarged sources and the specified enlarged precomposition
  equivalence. The independent universe `v` is retained, including `v = 0`, `v = u`, and
  strict enlargement.
- The node's final convention, that no finite simplex-category assumption is made, is
  reflected by the absence of any finiteness or nonemptiness hypothesis.

The dependency signatures were checked in full. `def-cbc-enhanced-diagrams-cones` supplies
`Enhanced.fullSubcomplex` and `Enhanced.IsFunctorEquivalence`; it does not introduce a
second functor-category notion. `lem-coef-marked-relative-cartesian-model` supplies the
actual slice `Over`, `funOver`, `PreservesMarkings`, `cartesianFunctors`, `IsNaturallyFibrant`,
`weak`, `pull`, and `productMapLeft`. The helper declarations in this module use those
recorded declarations directly. No dependency mismatch or private replacement was found.

Edge cases checked against the node and definitions: `n = 0`; all degenerate simplices;
empty marked source; empty base (where the local quantifier is correspondingly empty);
identity and noninjective/nonfibrant maps; zero/empty simplicial sets; arbitrary markings,
including degenerate and all-edge markings; `S = Δ[0]`; and universe values `v = 0`,
`v = u`, and `v > u`. No hypothesis excludes any of these cases, and no finite index-set
assumption appears. The degreewise pullback in `pull` marks precisely the edges whose source
projection is marked, as required.

I repeated the three required existence searches. `msearch.py` LeanFinder for “marked
mapping simplex descent” returned only unrelated simplicial-set primitives; `msearch.py`
Loogle for `IsFunctorEquivalence` returned no match; grep over Mathlib, the upstream
`WeilConjectures`, this project's `lean/Sheaf`, and `dag/lean_names_upstream.json` found no
`marked_mapping_simplex_descent`, `functorRestriction`, `funOverPre`, `unmarkMap`,
`enlargeObject`, or `enlargeHom`. The existing `Marked.enlargeMap` was found and reused.
No Stacks tag states this notion; the source is the HTT propositions and remarks named in the
node and module header.

No mismatch was found, so no statement or definition was changed. The only postponed proof
remains the single named theorem `SSet.Marked.Over.marked_mapping_simplex_descent`; all
helper definitions have explicit data. The prescribed `scompile.py` compile of the module
completed cleanly with no diagnostics other than the permitted theorem `sorry`.

The independent LeanSearch query “A map of marked simplicial sets over a base is a
cocartesian equivalence if its pullbacks to all simplices are cocartesian equivalences”
returned only ordinary category cocartesian-arrow declarations and the inherited
model-category weak-equivalence instance on a slice, so no replacement declaration was
found. The HTT extract was checked at lines 8905–9035 (flat versus sharp mapping objects,
Remark the project server, Proposition the project server), 9100–9185 (the relative marked model structure), and
10460–10565 (the simplexwise gluing argument). The latter is explicitly an underlying
categorical-equivalence assertion, so the delivery correctly labels its marked adaptation
as agent-formulated rather than attributing that exact assertion to HTT the project server. The
recorded signature was also compared byte for byte with the theorem header: it agrees.
