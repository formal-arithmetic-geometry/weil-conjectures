## Worker report

Item: `lem-coef-simplicial-operator-nerve`, group Q03, stage 2.

The main module is `Sheaf.CategoryTheory.SimplicialOperatorNerve`. Its single postponed
 theorem is `CategoryTheory.SimplicialOperatorNerve.simplicial_operator_nerve`. It supplies
operator, unary and string categories with their full enriched presentations, the operad
assertion, the natural power-fiber comparisons, and the comparison of cocartesian
fibrations with the relative nerve of the actual power diagram. All theorem proofs are
`sorry`; the helper definitions have actual data. No construction is selected using
`Classical.choose`, `Nonempty.some`, or a postponed existence statement.

The category constructions are supplied together in the existence theorem, not defined
by choosing arbitrary data from it. Each is characterized up to enriched isomorphism:
object equivalences, mapping simplicial-set isomorphisms, all-degree identity and
composition formulas specify the entire enriched category. Projections are fixed on
objects and all edges into the ordinary nerve. This is precisely the equality used
subsequently: simplicial isomorphism for the strict fibers and coherent equivalence for
classification. The fiber comparisons are normalized on all enriched simplices, not
merely on objects. This presentation avoids proof-hole-dependent definitions.

The source was opened at https://arxiv.org/html/1312.3178v4, Definitions 3.1.6--3.1.7,
Lemma 3.1.8, Definition 4.2.2 and Proposition 4.2.3. The source's string fiber has n+1
coordinates, including C at [0], as already specified by this node. The resolved stage-1
repair note was read: it required re-splitting the proof and keeping the statement.
This delivery preserves that statement and every existing proof step and proof dependency.

Hypotheses and clauses, in source order:

| Node text | Lean rendering |
| --- | --- |
| Fixed small universe and sufficiently large ambient conventions | Explicit `universe u`; `SCat.{u}` has objects in `Type u` and mapping simplicial sets in `SSet.{u}`. Its collection of models and the existence theorem live in the larger universe automatically. |
| Use the specified coherent nerve and its conventions | `N : CoherentNerveComparisonStatement.{u}` is the comparison interface of the recorded dependency; its existence is `coherent_nerve_comparison`. The nerve used everywhere is the actual `CoherentNerve.nerveFunctor`, not a new nerve. The parameter fixes a representative of the already supplied comparison and is not an additional mathematical fibrancy assumption. |
| A nonsymmetric simplicial multicategory, with small colors | `SimplicialMulticategory.Data.Color`, `.operation`; added definition node `def-coef-simplicial-multicategory`. |
| Every finite ordered input list, including n=0 | `.operation (n : ℕ) (Fin n → Color) Color`; no positivity or nonemptiness binder. |
| Associative unital simplicial substitution | `.unit`, `.unit_natural`, `.substitute`, `.substitute_natural`, `.left_unit`, `.right_unit`, `.associativity`. `flatten` orders concatenated blocks by `finSigmaFinEquiv`. |
| Suppose every operation space is Kan | `SimplicialMulticategory.IsLocallyKan P` in `Statement.operator_operad`, quantifying over every n including zero. |
| Operator objects are finite color lists | `Word P.Color = (n : ℕ) × (Fin n → P.Color)`, and `OperatorModel.object`. |
| Coproduct over all order-preserving φ:[m]→[n] | The dependent sum in `operatorHom.obj` ranges over `⦋d.1⦌ ⟶ ⦋c.1⦌`, with no endpoint restriction. |
| Product of P on the blocks φ(i-1)+1,...,φ(i) | `operatorHom` uses `blockLength` and `blockIndex`. Lean uses zero-based color positions: the block begins at φ(i) and ends just before φ(i+1). |
| Composition is substitution | `OperatorModel.composition_base` and `.composition_operations`; the latter substitutes precisely the selected consecutive subfamily into the output operation. |
| Projection to Δᵒᵖ | `OperatorModel.projection`, `.projection_objects`, `.projection_edges`; the base arrow is the opposite of the mapping summand's φ. The base is the dependency's `monoidalSimplexBase`. |
| The coherent nerve is an ordinary nonsymmetric infinity operad | `Statement.operator_operad : ... → Nonsymmetric.IsOperad ...`, reusing all five conjuncts of the recorded predicate, including mapping-space relative limits. |
| Fiber at [1] is the unary coherent nerve | `UnaryModel` fixes unary operations, units and composition. `OperatorModel.inclusion` fixes its singleton inclusion on objects and mapping simplices. `.unaryFiber` is a simplicial isomorphism with normalization `.unaryFiber_normalization`. |
| Any small locally Kan simplicial category C | `C : SCat.{u}`, `IsLocallyKan C` in the relevant conclusion fields. Models themselves exist for all simplicial categories, as the source's construction does. |
| String objects (c₀,...,cₙ) | `String C = (n : ℕ) × (Fin (n+1) → C)` and `StringModel.object`; no empty string is added. |
| Displayed string mapping formula | `stringHom`: dependent sum over every monotone φ, with `(i : Fin (m+1)) → hom C (c (φ i)) (d i)` in every degree, and `StringModel.mapping`. |
| Its composition and projection | `StringModel.identity_base`, `.identity_components`, `.composition_base`, `.composition_components`, `.projection_objects`, `.projection_edges`; component composition is `eComp (f_{ψ(i)},g_i)`. |
| Its nerve is a cocartesian fibration | `Statement.string_cocartesian`, using the recorded `cocartesianFibrationOver`. |
| Classified by the coherent diagram [n]↦(N_hc C)^(n+1) | `Statement.comparison`, `.comparison_over`, `.comparison_equivalence`, `.comparison_cocartesian` compare it over the base to `Algebroid.domain (CoherentNerve.nerveFunctor.obj C)`, literally the relative nerve of `Algebroid.objectDiagram`. Thus the assertion retains the entire coherent classifying diagram, not merely a list of equivalent fibers. |
| Projection and diagonal transition functors | `.string_transport` uses `IsMonoidalTransport` and exactly `Algebroid.objectDiagram.map`: the opposite ordinal map selects the given coordinates in every simplicial degree. Injective maps omit coordinates and surjective maps repeat them. |
| Fiber at every [n] is the (n+1)-fold power | `Statement.string_fibers`; `StringFibers.iso` is a simplicial isomorphism. Its inverse is normalized by `.objects` and `.mappings`, the latter on every mapping simplex of every coherent simplex. `.comparison_fibers` normalizes the classifying comparison on all chains in a fiber. |
| Identifications natural in simplicial functors | `Statement.strings` is an actual ordinary functor on `SCat`; `.string_objects`, `.string_mappings` prescribe applying F to every entry; `.string_projection_natural` and `.comparison_natural` are commuting simplicial-map equations. Full simplex normalization of `StringFibers` then makes the fiber identifications natural as well. For multicategories, `.operator_maps` supplies `OperatorMap` with the same color/operation normalization, commuting unary inclusions and projections; faithfulness of the presented mapping isomorphisms forces identity/composition compatibility. |
| In particular, locally Kan simplicial groupoid gives a left fibration | `.groupoid_left` quantifies over the existing strict `SimplicialGroupoid` and its existing `.IsFibrant`, then asserts the recorded `leftFibration`. Its fibers are already the powers from `.string_fibers`. |

The full names of the additional statement dependencies are
`def-coef-simplicial-multicategory` (new) and `def-coef-simplicial-groupoid` (already landed).
The latter is needed to use the existing strict simplicial-groupoid definition rather
than making a second copy or replacing the hypothesis by a different notion.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.power`,
  `objectDiagram`, `domain`, `projection`, `domainMap`. Their bodies were read: `domain`
  is the relative nerve of precisely the finite-power diagram; its maps select coordinates.
- `Sheaf.CategoryTheory.OperadicAlgebraPresentability`:
  `SSet.Enhanced.Nonsymmetric.HasInertLifts`, `IsOperad`; the full signatures and all
  conjuncts were read, as was the nonsymmetric operadic-algebra interface.
- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, `coherent_nerve_comparison`,
  `CoherentMappingComparison`, including its vertex and all-dimensional normalization.
- Its recorded infrastructure: `CategoryTheory.CoherentNerve.SCat`, `hom`, `IsLocallyKan`,
  `underlying`, `nerveFunctor`; these are used directly, not redefined.
- `Sheaf.CategoryTheory.SimplicialGroupoid`:
  `CategoryTheory.CoherentNerve.SimplicialGroupoid` and `.IsFibrant`; full definition read.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence` with its coherent quasi-inverse conditions.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`:
  `SSet.Enhanced.cocartesianFibrationOver`, publicly reexporting the recorded `fiber`,
  `leftFibration`, `preservesCocartesianEdges` and `IsCocartesianEdge` interface.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`:
  `monoidalSimplexBase`, `monoidalBaseVertex`, `monoidalBaseEdge`,
  `monoidalFiberInclusion`, `IsMonoidalTransport`.
- Mathlib: `SSet`, `SSet.KanComplex`, `EnrichedCat`, `EnrichedFunctor`,
  `EnrichedCategory.eId/eComp`, `SimplexCategory`, `finSigmaFinEquiv`.

All recorded proof-dependency modules are imported, privately when proof-only.
`lem-coef-cocartesian-right-kan-extension-simplex-powers` and
`lem-coef-cocartesian-straightening` have no Lean record on the base and therefore no
module to import. Their arguments remain explicitly cited in the proof docstring;
neither missing proof is used as a statement assumption or as data for a definition.
The relative-nerve formulation uses the already available `Algebroid.objectDiagram`
and does not require inventing a second classifying functor.

Edge cases checked before and during writing:

- Empty color set: unary category empty; operator category retains just the empty list.
- Length-zero operator source or target: all indices still have their stated types;
  an arrow to the empty target has no operations; an arrow out of an empty source
  requires the actual product of nullary operations.
- Empty nullary operation space: admissible and Kan; relevant mapping summands may
  be empty. No chosen nullary element or nonemptiness assumption occurs.
- Constant/non-surjective base maps, repeated indices, and unused end blocks:
  all monotone maps appear in the dependent sum; only the specified blocks enter
  substitution. The three-level equation permits zero-length intermediate blocks.
- Unary fiber [1]: the identity base summand is used; constant base maps are not
  silently retained in the fiber. The singleton inclusion is normalized on all simplices.
- String fiber [0]: C, not a point or an empty power. Every string has n+1 entries.
- Empty simplicial category: every string fiber and its relative nerve are empty;
  cocartesian and left-fibration lifting conditions are vacuous with empty domain.
- Terminal simplicial category: each string fiber is a point; transitions are its
  unique maps. The same model supports arbitrary non-groupoidal locally Kan C.
- Faces and degeneracies: the fixed `objectDiagram.map` omits or repeats coordinates,
  including maps to/from [0]. The normalization includes all mapping simplices.
- Arbitrary small universe u is explicit. No auto-bound variables, restricted
  cardinality, extra arity positivity, or equality of independent site universes.

Searches for existing statements/notions (all 2026-10-17):

- `msearch.py ... leanfinder` query "The coherent nerve of the category of operators
  of a locally Kan nonsymmetric simplicial multicategory is a nonsymmetric infinity
  operad": returned the ordinary nerve, its quasicategory/Segal facts and
  `CategoryTheory.SimplicialNerve`; none is the requested construction/theorem.
- `msearch.py ... loogle 'SimplicialCategory, nerve'`: 0 hits, unknown unqualified
  identifier `SimplicialCategory`. The qualified local source was then read directly.
- `msearch.py ... leansearch 'simplicial multicategory nonsymmetric operad category of
  operators'`: eight hits for SSet, simplex/simplicial objects, simplicial categories
  and their nerve, not a multicategory.
- `msearch.py ... grep 'Multicategory|multicategory|operatorCategory|stringCategory'
  CategoryTheory`: 0 Mathlib hits. Same regex over the full upstream
  `WeilConjectures` and side `lean/Sheaf`: no hits.
- `rg` for `SimplicialMulticategory|SimplicialOperatorNerve` in upstream names,
  upstream source and side Lean: no existing declaration.
- Exact node-id `grep -rn` in upstream source: no hit.
- `blueprint_refs.py search 'simplicial multicategory'`: 0 blueprint nodes.
  DAG text matches the assigned item and its two consumers only; none is a
  preexisting definition node for the multicategory structure.
- Additional local source search found `finSigmaFinEquiv` in
  `Mathlib.Algebra.BigOperators.Fin`, and the existing strict groupoid module/node.

No statement correction, disputed statement, dependency-module repair or tool fault.

## New nodes

`def-coef-simplicial-multicategory` defines the nonsymmetric simplicial multicategory
used by the item's first paragraph, local Kan fibrancy of all operations and its
simplicial multifunctors. It follows GH Definition 3.1.6 and the functorial operator
construction of Definition 3.1.7. Its own module is
`Sheaf.CategoryTheory.SimplicialMulticategory`; its data and all substitution/unit laws
are explicit, including nullary operations and the full three-level associativity
formula. HEq suppresses only the provably equal arities and ordered color functions
obtained from reindexing finite sums. The four search records retain the searches
above. Mathlib's `SimplicialCategory` only supplies binary hom objects, so it cannot
serve as this missing notion. No existing definition node or project declaration
supplies it. The item's statement dependencies gain this id.

## Second reading by Q03

This is the assigned worker's separate clause-by-clause reread, with the node and
both modules open. No other agent was started, as the dispatcher brief requires;
the maintainer supplies the independent delivery review.

The read-through checked every row of the correspondence table against the final
structure fields. It found and repaired the following issues during preparation:

1. Fully qualify `CoherentNerve.nerveFunctor` to avoid resolving to the ordinary
   category nerve functor.
2. Replace the initially broader π₀-groupoid specialization with the existing
   strict `SimplicialGroupoid` hypothesis, and cite its already landed definition node.
3. Supply the required commuting equation to `preservesCocartesianEdges`.
4. Normalize string fibers on every coherent simplex and every enriched mapping
   simplex, and normalize the relative-nerve comparison on every chain in each fiber.
5. Keep base maps unrestricted, empty operator lists, nullary products, the [0]
   string fiber and all simplicial degrees. The coordinate-selection transition is
   the existing actual diagram, and the comparison retains cocartesian edges.

The multicategory module has no postponed theorem. The only `sorry` in this delivery
is the main item's named theorem. Its docstring follows all eleven existing proof
steps, including the split right-Kan and marked-model arguments. All variables and
universes are explicitly bound. All writes are confined to the assigned sandbox.

## Returned-delivery repair (immutable head df723ae32003)

The saved packet first passed `deliver2.py ... --no-push` as commit `7f6b94643d`.
The return compares two signatures printed with an unqualified `Statement`. They
resolve to different structures because the declarations are in different namespaces.
I read the current `Sheaf.CategoryTheory.CofibrantSimplicialInversion` source both
in the shared checkout and through `scompile.py --source` before making this repair.
Its theorem has the fully qualified type

```lean
(N : CategoryTheory.CoherentNerveComparisonStatement.{u}) →
  Nonempty (CategoryTheory.CofibrantSimplicialInversion.Statement.{u} N)
```

That structure specifies `completion`, `unit`, `inversion`, degreewise localization,
`ordinary_pushout`, `homotopy_pushout` and `total_inversion_nerve`. It does not specify
operator categories, string categories, nonsymmetric operads or power-fiber comparisons.
The present theorem has the fully qualified type

```lean
(N : CategoryTheory.CoherentNerveComparisonStatement.{u}) →
  Nonempty (CategoryTheory.SimplicialOperatorNerve.Statement.{u} N)
```

Its structure instead specifies `operators`, `operator_operad`, `strings`,
`string_model`, `string_fibers`, `string_cocartesian`, `comparison`, the naturality
and normalization equations, and `groupoid_left`. These are the clauses of this node
matched in the table above. The cofibrant-inversion theorem therefore cannot replace
it. The repair follows the return's alternative instruction to make differing binders
explicit: the source signature now fully qualifies both the comparison binder and the
result structure, including universe arguments. The node's `lean.statement` is the
verbatim repaired signature. This changes no mathematical hypothesis or conclusion,
adds no proof, and retains the saved definitions and proof docstring.

Self-check of the repair: the current shared-main node and the sandbox node differ
only in `lean` and the two previously added definition dependencies. The resolved
stage-1 repair note still requires no statement change. The added multicategory node
is absent from current main, so its saved module and node remain required. The
original second reading and all edge-case checks above remain applicable; in
particular arity zero and the string fiber at [0] are unaffected. No declaration
from `CofibrantSimplicialInversion` is used by this node's statement or proof plan,
so adding its import would be unused. The qualified result identifies the intended
operator/string structure directly, independent of namespace resolution.

## Dependency modules

The first retry reproduced the published overlay failure in
`Sheaf.CategoryTheory.SpaceValuedStraightening`: `Diagrams` used the
noncomputable `smallSpaces` without a `noncomputable` marker. I copied the recorded
dependency node and its module into this packet, changing only that declaration to
`noncomputable abbrev Diagrams`; all imports, definitions, statements and theorem
signatures are unchanged. The copied node's `lean.note` records this repair, with
`by` Q03 and the current date. The side module is included so the item's transitive
`CompleteAlgebroid` import compiles against the corrected interface.

The repair is a §1(B) dependency-module repair, not a statement change: no hypothesis
or conclusion of this item or of the dependency is altered. The module is owned by
`lem-coef-space-valued-straightening` in the copied node record.
