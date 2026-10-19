## Worker report

The module `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation` states
`SSet.Enhanced.cartesian_mapping_simplex_presentation`. No existing exact statement was
found. The original node is unchanged except for `lean`; there is no statement correction,
dependency repair, or new independent notion/node.

Clause-by-clause rendering:

- Small simplicial sets use Mathlib `SSet.{u}` throughout, for an arbitrary explicit universe
  `u`. The nonnegative dimension is the unrestricted binder `n : ℕ`.
- A chain `A₀ ← … ← Aₙ` is `SimplexChain n`, an abbreviation for Mathlib's existing functor
  type `(Fin (n + 1))ᵒᵖ ⥤ SSet.{u}`. It imposes no quasicategory condition on the `Aᵢ`.
- `MappingSimplexDegree A r` is exactly the dependent pair of an order homomorphism
  `α : Fin (r.unop.len + 1) →o Fin (n + 1)` and a simplex of
  `A.obj (op (α (Fin.last r.unop.len)))` in degree `r`.
- `mappingSimplexOperator A θ` first applies the fibre's simplicial `map θ`, then the
  chain's map from the old last vertex to the new last vertex. The inequality used is
  monotonicity of `α` and the bound of the new last image by the old last vertex.
  `mappingSimplex` uses those exact operators, and `mappingSimplexProjection` returns `α`.
- `markedMappingSimplex.marking` requires precisely `e.2 ∈ Set.range (Aᵢ.σ 0)`, with
  `i = e.1 (Fin.last 1)`. The first conjunct of the theorem gives the marked isomorphism
  from `Marked.flat (A.obj (op i))` to the pullback fibre. Its equation with the pullback
  projection pins the isomorphism to `mappingSimplexFiberInclusion`, the actual constant
  base inclusion, rather than an arbitrary fibre equivalence.
- A small naturally marked Cartesian fibration is quantified as
  `Y : Marked.Over (Δ[n] : SSet.{u})` with `Marked.Over.IsNaturallyFibrant false Y`.
  This is exactly a Cartesian fibration and its exact Cartesian-edge marking, by the
  recorded relative-model dependency. It does not impose extra data or fibrancy on `A`.
- The second conjunct quantifies every such `Y`, and asserts existence of a chain and
  `q : mappingSimplexOver A ⟶ Y`. Slice morphisms preserve markings and commute with the
  base projection. The canonical `mappingSimplexPresentationFiber A q i` is obtained by
  the degreewise pullback universal property from the inclusion followed by `q`.
  Every one of these maps satisfies `CoherentNerve.IsCategoricalEquivalence`.
- The third conjunct quantifies every chain, every such `Y`, and every marked map `q`
  over the simplex. Its sole additional hypothesis is the stated categorical-equivalence
  property for every vertex fibre. The conclusion is `Marked.Over.weak false q`, the
  dependency's Cartesian equivalence in the relative model.
- The fourth conjunct is the equivalence of the two fibrewise hypotheses. The alternate
  hypothesis is `Marked.weak (flatToNaturalMap (mappingSimplexPresentationFiber A q i))`
  for every `i`. Its source is exactly `Aᵢᶠˡᵃᵗ`; its target is the absolute natural
  marking of the actual target fibre. `flatToNaturalMap` is the canonical same underlying
  map, preserving degenerate edges by naturality. The absolute dependency identifies
  that natural marking with equivalence edges of a quasicategory.

The theorem has four conjuncts because the first supplies the specified marked vertex
fibres, in addition to existence, the criterion for every map, and the equivalent absolute
model formulation. All data definitions are explicit. The construction laws postponed as
named theorems belong to the construction already required by this same DAG node:
`mappingSimplexOperator_laws`, `mappingSimplexFiber_naturality`,
`mappingSimplex_degenerate_marked`, and `mappingSimplexFiber_projection`. Each has its
source/blueprint docstring and complete argument; each is listed in `lean.declarations`.
The final theorem's docstring records the node's full induction, mapping-space comparison,
marking-reflection and mapping-test proof route. Every theorem proof is exactly `sorry`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.coneCategory` is the
  recorded declaration; the relevant primitives in that module are
  `IsEquivalenceEdge`, `core`, and `IsWeakHomotopyEquivalence`, used by the recorded
  model interfaces. Mathlib supplies `SSet`, standard simplices, ordinal order maps,
  simplicial maps and degreewise pullbacks.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over.marked_relative_cartesian_model`, `Over`, `relativeFibration`,
  `IsNaturallyFibrant`, `pull`, and `weak`. Read the slice and natural-marking formulas,
  the model statement and its fibre criterion. The present map is allowed a nonfibrant
  source, unlike that dependency's fibrant-object fibre criterion.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`, with categorical-equivalence testing by homotopy
  categories of functor objects, every dimension, and arbitrary containing universes.
  The actual predicate used is `SSet.CoherentNerve.IsCategoricalEquivalence`, already
  used as `Marked.Over.categoricalEquivalences` by the relative-model dependency;
  its full definition in `CoherentNerveInfrastructure` was read. It tests restriction
  on cores against every small quasicategory and applies to nonquasicategory sources.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked.marked_point_cartesian_model`, `Marked`, `flat`, `natural`, `sharp`,
  and `weak`. The definitions retain degenerate edges in the natural marking;
  the model theorem identifies it with equivalence edges.

All proof dependencies with recorded modules are imported without `public`, except where
already direct statement imports. Two proof prerequisites have no recorded module in the
read snapshot: `lem-coef-infinity-cocartesian-mapping-criterion` and
`lem-coef-mapping-simplex-final-edge`;
they are proof-only, so no replacement statement or extra hypothesis is introduced.

Edge cases checked before stating:

- `n = 0`: every `α` is constant, all transitions are identities; the construction is
  exactly `A₀` with flat marking. The theorem reduces to the one-fibre presentation
  and the absolute flat-to-natural test. There is no positive-dimension hypothesis.
- Empty fibres are permitted by the unrestricted functor to `SSet`; a degreewise sigma
  may be empty. No inhabitance, chosen vertex, or nonempty fibre is required anywhere.
  The empty total Cartesian fibration is included by the same binders.
- The chain may contain nonquasicategories. Only its target is naturally fibrant;
  no fibrancy assertion is made about the mapping simplex.
- Marking is exact, not the set of all edges nor all Cartesian edges. Over a single
  vertex it remains the flat marking even when the fibre has nondegenerate equivalences.
- The arbitrary-map criterion does not restrict `q` to the map produced by existence.
- All fibre sets and constructions stay in `u`; the collection of chains is allowed
  in the containing universe of all such small objects, without a size restriction.

Searches (performed with the prescribed `msearch.py`):

- LeanFinder: `marked mapping simplex M^m chain simplicial sets Cartesian fibration`.
  Eight hits: standard-simplex constructors, simplicial operators, and unrelated Kan
  pointed-simplex mapping structures; none constructs this mapping simplex.
- Loogle: `mapping simplex, simplicial set, Cartesian fibration` returned zero hits
  (unknown identifier `mapping`), so it supplies no positive evidence.
- Mathlib grep: `mapping.?simplex|MappingSimplex|marked.?mapping`, subdirectory
  `Mathlib`, returned zero hits. A later unrestricted Mathlib grep was also run.
- LeanSearch: `marked mapping simplex of a chain presents a Cartesian fibration over a
  standard simplex` returned eight hits on ordinary fibre categories, standard simplices
  and simplex-category generators, with no matching statement or construction.
- Direct `rg` in `WeilConjectures`: the item ID, `MappingSimplex`, `mappingSimplex`,
  and `mapping.?simplex` returned no hits. The exact item-ID search returned no hits.
- Direct `rg` in `lean/Sheaf`: no exact mapping-simplex construction existed. The nearby
  `EnhancedCartesianFibration.grothendieck` was read: it is the cocartesian initial-vertex
  construction for a strict diagram of **quasicategories**, whereas this node uses
  arbitrary simplicial sets and final-vertex contravariance. Reusing it would add an
  excluded quasicategory hypothesis. The chain itself reuses Mathlib's functor type.

Source verified directly: downloaded the cited HTT PDF into this sandbox and read its
Section 3.2.2, pp. 179–180, 183–185 and 187. The dependent pairs and marking are exactly
those before Remark the project server and in Notation the project server. Definition the project server gives the three
presentation conditions. Proposition the project server(1) gives existence, the project server–11 give the
categorical comparison and inductive construction, and the project server gives Cartesian
equivalence. No source correction is necessary. The PDF explicitly warns in Remark
the project server that the mapping simplex need not be a Cartesian fibration.

Validation: the full module, including all available proof-dependency imports, was
compiled by the prescribed `scompile.py` wrapper. Both sandbox and final module-name
checks passed with no errors or warnings. The required `deliver2.py --no-push` dry run
also recompiles the file before server preflight.

Completion check (2026-10-17 UTC): reread the existing sandbox against the current node
and all four statement-dependency interfaces. The current node still differs only in `lean`.
Updated the UTC date and made the absolute marked-model statement import public.
The newly available proof dependency `lem-coef-relative-marked-anodyne-calculus` is now
imported without `public`; the other two unstated proof-only prerequisites remain listed above.
A fresh wrapper compile was clean. The delivery dry run printed OK, with only the expected
second-reading exception reserved for the independent reader; nothing was pushed.

## Second reading by Q04

I opened the current node, its HTT source place, all four statement dependencies, and the
Lean module. The node's objects and clauses match the following Lean declarations.

- The fixed natural number `n : ℕ` is the theorem parameter. `SimplexChain.{u} n` is the
  functor `(Fin (n + 1))ᵒᵖ ⥤ SSet.{u}`, so it represents exactly a finite chain
  `A₀ ← … ← Aₙ` of small simplicial sets, with no quasicategory or nonempty-fibre
  hypothesis.
- For `r : SimplexCategoryᵒᵖ`, `MappingSimplexDegree A r` is the dependent pair of an
  order map `α : Fin (r.unop.len + 1) →o Fin (n + 1)` and an `r`-simplex in the fibre at
  the final value `α (Fin.last r.unop.len)`. This is the node's `(α,a)` construction.
- `mappingSimplexOperator` first applies the simplicial operator to `a` and then the
  contravariant chain transition from the old final index to the new final index;
  `mappingSimplexOperator_laws` supplies the identity and composite laws used by
  `mappingSimplex`.
- `mappingSimplexProjection` is the monotone-map projection to `Δ[n]`. The fibre
  inclusion `mappingSimplexFiberInclusion` uses the constant order map at `i`, and
  `mappingSimplexFiber_projection` states that its composite with the projection is
  the constant vertex map.
- `markedMappingSimplex` marks exactly those 1-simplices whose final-fibre coordinate
  lies in the range of `σ 0`; this is precisely the source's degenerate-coordinate
  marking. `mappingSimplexOver` packages this marked mapping simplex over `Δ[n]`.
- `mappingSimplexPresentationFiber` is the canonical pullback fibre map induced by the
  inclusion and an over-map `q`; the first conjunct of the theorem supplies a marked
  isomorphism from `Marked.flat (A.obj (op i))` to this pullback object and requires its
  composite with the pullback projection to equal the canonical inclusion.
- A small Cartesian fibration is rendered as `Y : Marked.Over (Δ[n] : SSet.{u})` with
  `Marked.Over.IsNaturallyFibrant false Y`; this supplies exactly the underlying
  Cartesian fibration and its Cartesian-edge natural marking. The existence conjunct
  quantifies every such `Y` and gives `A` and `q : mappingSimplexOver A ⟶ Y`, with a
  `CoherentNerve.IsCategoricalEquivalence` on every vertex-fibre map.
- The universal criterion quantifies every chain, every such `Y`, and every marked over
  map `q`; its only fibrewise hypothesis is categorical equivalence at every vertex and
  its conclusion is `Marked.Over.weak false q`, the recorded relative Cartesian model
  equivalence.
- The final conjunct has the same quantifiers and is exactly the equivalence between
  those categorical-equivalence fibre maps and
  `Marked.weak (flatToNaturalMap (mappingSimplexPresentationFiber A q i))` for every
  `i`. `flatToNaturalMap` has the canonical underlying fibre map and marks the target
  by the natural marking.

The source reading was HTT §3.2.2, especially Remark the project server, Notation the project server,
Definition the project server, Propositions the project server(1), the project server, the project server, and the project server. The
source confirms the final-vertex contravariance, exact degenerate marking, fibrewise
categorical-equivalence condition, and relative Cartesian-equivalence conclusion. The
Lean includes the source's `n = 0` case and permits empty fibres and an empty total
space. It does not assert that the mapping simplex is fibrant, as explicitly warned in
Remark the project server. All objects use the single arbitrary simplicial-set universe `u`; no
universe equality, characteristic, finiteness, or Noetherian assumption is introduced.

I searched independently with `msearch.py` LeanFinder, LeanSearch, and grep queries for
mapping-simplex and Cartesian-fibration constructions; LeanFinder and LeanSearch returned
only unrelated standard-simplex, nerve, or ordinary-fibration declarations, and grep found
no matching Mathlib declaration. Direct `rg` searches in `WeilConjectures/`, the existing
`lean/Sheaf/` tree, and the upstream-name index found no exact notion or theorem. The
nearby `EnhancedCartesianFibration.grothendieck` is a different cocartesian construction
for quasicategory-valued diagrams and cannot replace this arbitrary-simplicial-set,
final-vertex construction. The four recorded dependency modules were opened and their
interfaces are used directly; no dependency module or definition node is missing.

No mismatch was found, so no Lean or node repair was necessary. The only delivery change
is this independent second-reading record. `scompile.py` compiled the module cleanly with
no errors or warnings beyond the permitted `sorry` declaration warning.
