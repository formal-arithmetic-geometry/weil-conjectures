## Worker report

The module `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap` defines
`SSet.Enhanced.IsUniversallyLocalizing`, together with its two constituent constructions
`edgeInvertingDiagrams` and `IsLocalizationAtEdges`. These are the notions explicitly
introduced by this item's statement, so all three belong to this node. There are no
new nodes, dependency repairs, statement corrections, theorem statements, or `sorry`s.
Only the item's `lean` field changes; its original `status` is retained.

Sources read online on 2026-10-17: Kerodon Definition the project server,
<https://kerodon.net/tag/02M0>, and Proposition the project server(2),
<https://kerodon.net/tag/01MS>, reached through the cited subsection
<https://kerodon.net/tag/02LZ>. These give exactly the arbitrary-simplicial-set,
functor-category formulation used in the node. No quasicategory assumption on the
source, target, or base-change shape is needed.

Clause-by-clause correspondence:

- Small simplicial sets and a simplicial map `f : A → B` are
  `{A B : SSet.{u}} (f : A ⟶ B)` in both predicates.
- The collection of edges is `W : Set (A _⦋1⦌)`. It need not contain degeneracies,
  be closed under composition, or satisfy any other extra condition.
- For every test quasicategory is
  `∀ (E : SSet.{max u v}), Quasicategory E →` in `IsLocalizationAtEdges`.
  The explicitly declared independent universe `v` allows any larger containing
  universe. `SSet.uliftFunctor.{v, u}` transports the small sets and map degreewise;
  it adds no mathematical restriction on them and preserves their simplices.
- The functor simplicial set is Mathlib's `(ihom K).obj E`, the internal hom
  used by the recorded dependency. In this module `K` is the lifted small domain.
- Sending each edge of `W` to an equivalence is
  `∀ e : A _⦋1⦌, e ∈ W → IsEquivalenceEdge E (...)`.
  For a functor vertex `h`, its evaluation on that edge is
  `h.app (op ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op (ULift.up e)`.
  The ordinal map is the unique map `[1] → [0]`; this is exactly the evaluation
  convention in the dependency's `equivalenceDiagrams`, restricted to `W`.
- The full subcategory on those diagrams is `fullSubcomplex` applied to that
  vertex predicate, named `edgeInvertingDiagrams A W E`. It includes every
  simplex whose vertices satisfy the predicate, retaining all higher simplices.
- Precomposition by `f` is
  `(MonoidalClosed.pre (SSet.uliftFunctor.{v, u}.map f)).app E`.
- Factoring through the specified full subcategory is the existential map `r`
  with source `Fun(B,E)` and target `(edgeInvertingDiagrams A W E).toSSet`,
  and the equation `r ≫ (edgeInvertingDiagrams A W E).ι = ...pre...`.
  This is equality of actual simplicial maps in every degree.
- Inducing a functor equivalence onto the full subcategory is
  `IsFunctorEquivalence r`. This is precisely the dependency's predicate using
  a quasi-inverse and coherent natural equivalences of both composites.
- Every small base-change map is `∀ (T : SSet.{u}) (g : T ⟶ B)`.
- The degreewise pullback and its projection to `T` are `pullback g f` and
  `pullback.fst g f`. Simplicial sets are presheaves; Mathlib's functor-category
  limits are computed pointwise. Read `SimplicialObject/Basic.lean`'s limit
  instances and `Limits/FunctorCategory/Basic.lean`'s
  `functorCategoryHasLimitsOfShape` and `evaluation_preservesLimitsOfShape`.
- The collection for this base change is
  `∃ W : Set ((pullback g f) _⦋1⦌)`, followed by
  `IsLocalizationAtEdges.{u, v} (pullback.fst g f) W`.
  Thus the order is `∀ T g, ∃ W, ∀ E, ...`: `W` may depend on `g`, and the
  factorization may depend on `E`, but `W` cannot depend on `E`.
- There are no `Quasicategory A`, `Quasicategory B`, or `Quasicategory T`
  hypotheses. The only quasicategory condition is on the test `E`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, `SSet.Enhanced.IsEquivalenceEdge`, and
  `SSet.Enhanced.IsFunctorEquivalence`. Read the whole module, including
  `AreNaturallyEquivalent`, `diagramVertex`, and `equivalenceDiagrams`, to
  check the coherent equivalence and diagram-evaluation conventions.
- Its public Mathlib imports provide `SSet.Quasicategory`, `SSet.uliftFunctor`,
  `CategoryTheory.ihom`, `CategoryTheory.MonoidalClosed.pre`, and subcomplex
  inclusion `SSet.Subcomplex.ι`. No private substitute is introduced.

Edge cases checked before settling the definitions:

- Empty `W`: the inversion predicate has no obligations, so the full functor
  category is retained. This is the correct equivalence-localization case.
- All edges in `W`: the same evaluation formula specializes to the dependency's
  all-edge-inverting diagram convention; no closure hypotheses are added.
- Empty `A` or `T`: sets of degree-one simplices and subcomplexes still exist;
  there is no nonemptiness assumption. In particular the empty base-change
  shape is tested, not omitted.
- Empty test quasicategory `E`: it is included by the unrestricted quantifier.
  For instance the empty-to-point map cannot spuriously pass localization:
  `Fun(point, empty)` is empty whereas `Fun(empty, empty)` has its unique
  diagram. An equivalence onto the latter cannot exist.
- Identity maps: with no edges forced, the restriction-equivalence formulation
  is the expected identity equivalence, including after base change.
- Arbitrary non-quasicategory shapes are accepted for `A`, `B`, and `T`.
  Larger test universes use `max u v` and the actual degreewise lift; no equality
  of the small and test universes is imposed.

Searches for an existing definition (all run for this item on 2026-10-17):

- `msearch.py ... leanfinder`: query
  "A simplicial map exhibits its target as localization at edges if restriction
  of functor quasicategories is an equivalence onto diagrams inverting the edges".
  Eight hits, including `CategoryTheory.Functor.q_isLocalization`,
  `CategoryTheory.Localization.functorEquivalence`, and ordinary localizer
  equivalences. None defines localization of arbitrary simplicial sets.
  Read Mathlib `CategoryTheory/Localization/Predicate.lean`: its
  `Functor.IsLocalization` takes ordinary categories and an ordinary functor.
- `msearch.py ... leansearch`: query
  "Universal localization of a map of simplicial sets at a collection of edges
  detected by functor quasicategories". Eight hits, all ordinary category,
  module, or derived-category localizations, including `Functor.IsLocalization.mk`
  and `mk'`; none is this notion.
- `msearch.py ... loogle 'SSet, Localization'`: zero hits.
- `msearch.py ... grep 'universally.?[Ll]ocaliz|[Uu]niversal[Ll]ocaliz'`:
  zero Mathlib hits.
- `rg` for the same universal-localization expression in upstream
  `WeilConjectures/` and project `lean/Sheaf/`: no hits. The requested node-id
  search in upstream `WeilConjectures/` also found no hits.
- Exact-name `rg` for `edgeInvertingDiagrams|IsLocalizationAtEdges|IsUniversallyLocalizing`
  in Mathlib, upstream `WeilConjectures/`, project `lean/Sheaf/`, and
  `dag/lean_names_upstream.json`: no hits before this sandbox module.

Validation: the required `scompile.py Q45 def-coef-universally-localizing-simplicial-map`
compiled the delivered file cleanly, with no warnings. All variables and universes
are explicitly bound, and the module sets `autoImplicit false`. The final delivery
check is the required `deliver2.py ... --no-push`; the independent second reader
will write their own reading and deliver.

## Second reading by Q45

The node statement was checked clause by clause against Kerodon Definition the project server (02M0),
Proposition the project server(2) (01MS), and the recorded dependency `def-cbc-enhanced-diagrams-cones`.
The Lean rendering and verdict for each introduced object and clause are:

- Small simplicial sets `A B : SSet.{u}` and a map `f : A ⟶ B` are the binders of
  `IsLocalizationAtEdges`; no quasicategory, Kan, finiteness, or nonemptiness assumptions are
  added. Verdict: matches.
- The edge collection `W ⊆ A _⦋1⦌` is the explicit `Set` argument. It is arbitrary, with no
  closure or degeneracy condition. Verdict: matches.
- `edgeInvertingDiagrams A W E` transports the existing
  `CategoryTheory.EnrichedMarkedRealization.invertingDiagrams` to the lifted domain with
  the edge collection `{e | e.down ∈ W}`. Its implementation uses `fullSubcomplex` on
  vertices evaluating to equivalence edges, retaining all coherent transformations and
  higher simplices. Verdict: matches the full subcategory of `W`-inverting diagrams.
- `IsLocalizationAtEdges` quantifies `E : SSet.{max u v}` with `Quasicategory E`, then
  existentially supplies `r : Fun(B,E) ⟶ edgeInvertingDiagrams A W E` and requires the exact
  factorization equation through `edgeInvertingDiagrams.ι`, together with
  `IsFunctorEquivalence r`. Verdict: matches precomposition factoring through and inducing a
  coherent functor equivalence; the factorization and equivalence are in the right order.
- `IsUniversallyLocalizing` quantifies every `T : SSet.{u}` and `g : T ⟶ B`, then chooses
  `W : Set ((pullback g f) _⦋1⦌)` before invoking
  `IsLocalizationAtEdges.{u,v} (pullback.fst g f) W`. Verdict: matches the degreewise pullback
  projection, and the collection depends on `g` but is independent of `E`.
- The `ULift` transport and `max u v` test universe implement “enlarging universes as needed”
  without identifying the small and test universes. Verdict: matches.

Edge cases were checked: `W = ∅` imposes no inversion conditions; taking all degree-one edges
imposes the all-edge condition; empty `A`, `T`, or `E` remains admitted; identity maps use the
empty collection; arbitrary non-quasicategory `A`, `B`, and `T` are allowed; and no condition
on characteristic, dimension, or a chosen vertex is present. The pullback and subcomplex
constructions remain defined in all these cases.

The duplicate searches were repeated with `msearch.py` (`leanfinder`, `leansearch`, `loogle`, and
`grep`), `rg` over the project `lean/Sheaf`, `rg` over upstream `WeilConjectures` and Mathlib,
and the exact names in `dag/lean_names_upstream.json`. New semantic queries included
“simplicial localization edge inverting diagrams” and “restriction into each quasicategory
identifies functors out of a simplicial set with diagrams carrying specified arrows to
invertible edges”. These found ordinary-category localizations and simplicial primitives.
The first new Loogle query `SSet localization` was ill formed; the replacement quoted-name
query `"SSet"` ran successfully, returning unrelated name matches. The successful LeanFinder
search and direct source searches supply the meaningful duplicate check.

The broader source search `localiz.*edge|edge.*localiz` found
`CategoryTheory.EnrichedMarkedRealization.IsEdgeLocalization` and `invertingDiagrams` in the
landed `Sheaf.CategoryTheory.EnrichedMarkedRealization` module. Both were opened and read.
`IsEdgeLocalization` requires its target `L` to be a quasicategory and explicitly requires
the marked edges to become equivalences in `L`; it is not the arbitrary-target predicate
of this node. Therefore it cannot replace `IsLocalizationAtEdges`, and no exact existing
declaration replaces `IsUniversallyLocalizing`. However, its `invertingDiagrams` is exactly
the full subcomplex construction needed here after universe transport. The original worker
had duplicated that construction. I replaced the body of `edgeInvertingDiagrams` by a
transported call to the existing helper, imported its module, and added its already landed
owning node `lem-coef-enriched-marked-realization` to `stmt_deps` (brief-stage2 §5 permits
adding a landed node with a Lean record). I read that node's statement and the helper
declarations against it. The added node has no path back to this item, so this introduces
no dependency cycle. No new node or dependency-module repair is needed.

The dependency declarations `fullSubcomplex`, `IsEquivalenceEdge`, and
`IsFunctorEquivalence` were read in full; their signatures agree with the uses here.
The original declaration's unique-map evaluation agrees with the existing helper's
`unitHomEquiv`/`Functor.natTransEquiv` evaluation: both recover the simplicial map from a
functor vertex. The transported edge collection includes exactly the lifts of `W`.

No mathematical statement correction was necessary. Besides eliminating the duplicate
construction, I added the required main-definitions list to the module documentation.
All definitions have real data, no theorem was proved, and there are no `sorry`s.
The definition node has empty proof steps, so a proof docstring is inapplicable. All three
declarations retain source/blueprint docstrings. Every variable and universe is bound;
`lean.statement` is verbatim the `def` signature before `:=`, and all delivered Lean lines
fit within 100 characters. The final module was recompiled with the required `scompile.py`
command, including its existing helper dependency, and completed without errors or warnings.
