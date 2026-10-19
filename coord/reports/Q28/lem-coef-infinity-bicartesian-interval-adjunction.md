## Worker report

The module `Sheaf.CategoryTheory.InfinityBicartesianIntervalAdjunction` states
`SSet.Enhanced.bicartesian_interval_adjunction`, with its sole theorem proof `sorry`.
It supplies explicit cylinder endpoints, strict fiber inclusions, and a predicate recording
the displayed canonical adjunct equivalences. No definition has postponed data. The interval
quasicategory instance is a term transporting Mathlib's proved nerve instance along
`stdSimplex.isoNerve 1`, using `innerFibrations.arrow_mk_iso_iff` and
`quasicategory_iff_innerFibration`; it introduces no new theorem or assumption.

Read the node and its four statement dependencies, including their statements, Lean
records, source modules, full signatures and docstrings. Read `def-coef-coherent-adjunction-data` and its recorded source to reuse the existing
general `CoherentAdjunction` structure. This independent definition-node binding is the
sole addition to `stmt_deps`, as explicitly requested in the maintainer return. The
downstream model-derived adjunction theorem is not a DAG dependency of this delivery.
The node statement, proof and other fields are unchanged. There are no new nodes or
repaired dependency modules.

Hypothesis and conclusion correspondence:

- Small quasicategories and coherent maps: `{E : SSet.{u}} [Quasicategory E]`, simplicial
  morphisms, and a single explicit arbitrary universe `u`. The fixed base is `Δ[1]`.
- Both fibration structures: `(hp : cartesianFibration p)` and
  `(hq : cocartesianFibration p)`. These are the recorded horn-lifting and prescribed-target
  or prescribed-source lift definitions, including `InnerFibration p`.
- Fibers `E₀,E₁`: `intervalFiber p 0`, `intervalFiber p 1` are abbreviations for the
  recorded `fiber p (stdSimplex.obj₀Equiv.symm i)`, not arbitrary categories with maps.
  `intervalFiberInclusion` is their actual pullback second projection.
- Given right transport: `R : intervalFiber p 1 ⟶ intervalFiber p 0`.
- Given full coherent cylinder: `h : Δ[1] ⊗ intervalFiber p 1 ⟶ E`.
  `h_over` says `h ≫ p = fst Δ[1] (intervalFiber p 1)` on all simplices.
- Endpoints: `h_zero` is the zero-end restriction `R ≫ intervalFiberInclusion p 0`;
  `h_one` is the one-end inclusion. `intervalEndpoint K i` is the actual map
  `lift (SSet.const (stdSimplex.obj₀Equiv.symm i)) (𝟙 K)`.
- Every edge of `h` at an object is cartesian: `h_cartesian` quantifies over every vertex
  `z` and tests `IsCartesianEdge p (lift (𝟙 Δ[1]) (SSet.const z) ≫ h)`.
- Existence of the left coherent functor and cylinder: the conclusion existentially binds
  `L : intervalFiber p 0 ⟶ intervalFiber p 1` and `k : Δ[1] ⊗ intervalFiber p 0 ⟶ E`.
- Its over-base condition is `k ≫ p = fst Δ[1] (intervalFiber p 0)`.
  Its two endpoint equations are the inclusion at zero and `L` followed by the inclusion
  at one. The next conjunct applies `IsCocartesianEdge` at every object `y`.
- The coherent adjunction is the existing
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction L R`, existentially bound as `adj`.
  Its `unitEdge`, `unit_src`, `unit_tgt` are exactly `id → RL` in the full internal hom
  `(ihom E₀).obj E₀`. Its `counitEdge`, `counit_src`, `counit_tgt` give `LR → id` in
  `(ihom E₁).obj E₁`.
- `adj.right_triangle` is a two-simplex in `Fun(E₁,E₀)` whose consecutive edges are
  `ηR`, `Rε` and whose long edge is the degenerate identity of `R`.
  `adj.left_triangle` is the analogous two-simplex in `Fun(E₀,E₁)`, with edges `Lη`,
  `εL` and identity long edge. These supply the requested homotopies of coherent
  transformations, including naturality at higher simplices. They are stronger data
  retention than equations solely in `hE₀` and `hE₁`, but are exactly the composition
  meaning of Kerodon Definition 6.2.1.1 (02EK), not an additional mathematical assumption.
- The explicit mapping-space equivalences are `IntervalAdjunctEquivalences adj`.
  For each `y`, `ηy` is a vertex in `mappingSpace C y (R(L(y)))`, with underlying edge
  fixed by `(evaluation C C y).app _ adj.unitEdge`. For every `z`, the tested map is
  `lift (mappingSpaceMap R (L.app _ y) z) (SSet.const ηy) ≫ c y (R(L(y))) (R(z))`.
  Thus it is exactly `v ↦ R(v) ∘ η_y`, and the conclusion is the recorded
  `IsWeakHomotopyEquivalence`, the equivalence notion for spaces.
- `c` is fixed up to simplicial homotopy by the canonical composition characterization:
  `j` is specified in every degree by the actual `rightPinchPrism`; `θ` and `ℓ` are
  the recorded consecutive/long triangle restrictions after their fixed inclusions;
  `r` is a homotopy inverse of `θ`; and the final homotopy says
  `c ≫ j ~ (j × j) ≫ r ≫ ℓ`. This is the characterization in the dependency's
  `MappingCompositionStatement`, with the same order of factors. No arbitrary composition
  or unspecified comparison map is substituted. Choosing representatives does not change
  the adjunct class.
- Coherent naturality in both variables is retained by the same `adj`: the unit/counit
  are full internal-hom simplices, and `adj.universal_unit` and `adj.universal_counit`
  assert initial/terminal objects in the actual coherent comma simplicial sets. These
  express representability naturally on full mapping spaces, including all parameter
  simplices. The explicit maps above are representatives of that represented adjunct
  class; no strictly natural selection of composition representatives is imposed.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `evaluation`, `diagramVertex`, `IsWeakHomotopyEquivalence`, and the
  coherent comma/initial/terminal conventions used by the existing adjunction.
- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.fiber`, `cartesianFibration`,
  `cocartesianFibration`, `IsCartesianEdge`, `IsCocartesianEdge`.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `SSet.Enhanced.triangleFiber`,
  `triangleEdgePair`, `triangleLongEdge`; the characterization and proof plan use
  `MappingCompositionStatement` and `mapping_composition`. Its public dependency
  `Sheaf.CategoryTheory.RightPinchComparison` supplies `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `rightPinchPrism`.
- `def-coef-coherent-adjunction-data`, recorded as existing in
  `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction` with the exact fields read above.
  It is general in the two simplicial sets and requires no model-category assumptions.
  The definition node depends only on `def-cbc-enhanced-diagrams-cones`; the Quillen
  theorem sharing its source module is not used as a DAG dependency.
- `Mathlib.AlgebraicTopology.Quasicategory.Nerve`: the existing nerve quasicategory
  instance, combined with `stdSimplex.isoNerve` and inner-fibration isomorphism invariance
  to construct the interval instance without an extra binder.

Sources opened online: [02FN](https://kerodon.net/tag/02FN),
[02FM](https://kerodon.net/tag/02FM), [019N](https://kerodon.net/tag/019N),
[01VN](https://kerodon.net/tag/01VN), [02EK](https://kerodon.net/tag/02EK),
and [02F1](https://kerodon.net/tag/02F1). The transport cylinders and their endpoint
orders match 019N/01VN; 02FM supplies their existence from reflection/coreflection;
02FN supplies the adjunction, 02EK its two functor-category triangles, and 02F1 the adjunct
formula. The node uses globally cartesian edges; over the interval these match the locally
cartesian transport condition in the definitions.

Edge cases checked mathematically before writing: empty total space permits both empty
fibers and empty cylinders; neither nonemptiness nor chosen objects are assumed. A nonempty
fiber at zero with empty fiber at one cannot satisfy the cocartesian lift hypothesis, and
the reverse mismatch cannot satisfy the cartesian hypothesis. Empty mapping spaces remain
allowed; equivalence means weak homotopy equivalence, including the component condition.
An identity/equivalence adjunction has degenerate unit/counit and triangle simplices and is
included. No equality of independent universe levels is imposed; all small data fit in
arbitrary `u`. There are no fiber-quasicategory hypotheses added merely for elaboration:
these follow from the given fibration. The standard interval is a quasicategory by the
explicit imported nerve construction, not a hollow hypothesis.

Searches for existing statements and names:

- `msearch.py ... leanfinder` query: “Opposite transports in a bicartesian quasicategory
  fibration over an interval are adjoint with coherent unit counit”. Eight hits: opposite
  equivalences, ordinary parametrized/quadruple adjunctions, and `SSet.Subcomplex.BicartSq`.
  No bicartesian interval transport theorem. Candidate signatures do not match.
- `msearch.py ... loogle` query: `"Adjunction", "Quasicategory"`. Zero hits.
- `msearch.py ... leansearch` query: “Bicartesian fibration over the interval induces a
  coherent adjunction of infinity categories”. Eight hits: ordinary section adjunction,
  ordinary cartesian composition, and bicategory adjunction constructors. Read the
  ordinary section/fibered-category signatures and Mathlib's QCat bicategory source;
  none states the interval theorem or supplies the required fibration hypothesis.
- `msearch.py ... grep` query: `bicartesian|[Aa]djunction|[Aa]djoint`, restricted to
  `AlgebraicTopology/Quasicategory`. Zero hits.
- `rg` of the source `WeilConjectures`, side `lean/Sheaf`, and upstream declaration
  census for `CoherentAdjunction|coherentAdjunction|bicartesian|interval_adjoint|intervalAdjoint`:
  only the existing `ModelInfinityDerivedAdjunction.CoherentAdjunction` in the side
  project supplies the adjunction notion, and is reused. No interval theorem.
- Required source grep for the exact item id: no matches.
- `rg` for all six proposed declaration names in Mathlib, upstream, the side project and
  the declaration census: no existing declarations.

Validation: `scompile.py Q28 lem-coef-infinity-bicartesian-interval-adjunction <module>`
compiled the sandbox and library forms cleanly, without warnings. Earlier elaboration
needed the standard-interval instance; it is now the explicit Mathlib transport term above.
All variables/universes are explicit (`autoImplicit false`); all lines are at most 100
characters. No statement dispute or node correction is needed.

## Repair of returned delivery 5b8f13508435

- H2/H12: removed the added `lem-coef-model-infinity-derived-adjunction` statement
  dependency and cited the existing `def-coef-coherent-adjunction-data` instead, exactly
  as requested. Its existing Lean record names the same `CoherentAdjunction` in the same
  imported module, so the theorem signature and constructions are unchanged. Updated
  `lean.note` and the worker report to distinguish the definition from the downstream
  Quillen theorem. Compared the retained sandbox node with the current shared main
  snapshot: only `lean` and this dependency addition differ. The prescribed delivery
  wrapper rebases these owned changes on current `newtargets-dag`.
- H8: replaced the incorrect “no split proof steps” paragraph with all seven current DAG
  proof steps verbatim, numbered 1–7 and naming every cited node. These cover fullness
  and opposite horn tests; pointwise reflection/coreflection; reflection assembly;
  the transport cylinders and edge tests; composite unit/counit and both triangles;
  conjugation to the prescribed right transport; and the canonical adjunct equivalence.

Validation of the repair: `scompile.py` compiled both the sandbox and library forms
cleanly (1.4 s and 1.7 s), with no errors or warnings. The stored Lean signature
matches the file. A read-only traversal of current DAG statement/proof dependencies
found no path from any of the four statement dependencies back to the item. The
replacement definition node has only the enhanced-diagrams definition as a dependency.

The previous second reading below is retained as the review of the returned version;
the dispatcher will arrange a fresh second reading of this repair before delivery.

## Earlier second reading (a previous round; superseded)

I independently opened the item node, its Kerodon source places (02FN, 02FM, 019N,
01VN, 02EK, and 02F1), the four statement-dependency records, and the complete Lean
module. The source's main assertion is the bicartesian interval transport adjunction;
the Lean statement renders every part as follows.

- The source's small infinity category `E` is `{E : SSet.{u}} [Quasicategory E]`.
  The map `p : E ⟶ Δ[1]` and both hypotheses `hp` and `hq` are respectively the
  recorded `cartesianFibration p` and `cocartesianFibration p`; no extra finiteness,
  nonemptiness, or fibrancy hypothesis is present.
- The source fibers `E₀` and `E₁` are `intervalFiber p 0` and `intervalFiber p 1`,
  with their actual pullback inclusions `intervalFiberInclusion p 0` and `p 1`.
  Thus they are strict fibers of `p`, not independently chosen quasicategories.
- The prescribed right transport is `R : intervalFiber p 1 ⟶ intervalFiber p 0`.
  Its coherent witness is `h : Δ[1] ⊗ intervalFiber p 1 ⟶ E`. The equation
  `h_over` is exactly the over-`Δ[1]` condition; `h_zero` and `h_one` give the
  source's endpoint order (R at 0 and the `E₁` inclusion at 1); and `h_cartesian`
  tests the required cartesian edge at every vertex of `E₁`.
- The existential conclusion introduces `L : intervalFiber p 0 ⟶ intervalFiber p 1`
  and `k : Δ[1] ⊗ intervalFiber p 0 ⟶ E`. Its four conjuncts are, in order, the
  over-base equation, the `E₀` inclusion at 0, the `L` inclusion at 1, and the
  cocartesian edge test for every vertex of `E₀`. These match the four clauses of the
  node without changing their quantifier order.
- `∃ adj : CoherentAdjunction L R` supplies the coherent unit and counit, their
  full-functor-category triangle simplices, and the universal comma objects. This is
  exactly the recorded model-infinity adjunction notion, rather than an ordinary
  homotopy-category adjunction. `IntervalAdjunctEquivalences adj` then supplies the
  node's explicit adjunct maps: its `ηy` is the evaluated unit vertex, and the map
  `lift (mappingSpaceMap R (L.app _ y) z) (SSet.const ηy) ≫ c ...` is precisely
  `v ↦ R(v) ∘ η_y`; it is asserted to be an `IsWeakHomotopyEquivalence` for every
  `y` and `z`. The `j`, `c`, `θ`, `ℓ`, and `r` fields fix the right-pinch and triangle
  restriction characterization from `MappingCompositionStatement`, so this uses the
  dependency's canonical composition class rather than an arbitrary map. The
  full-hom adjunction data supplies the stated coherent naturality.

No mismatch was found. In particular, the endpoint orientation, the strict fiber
objects, the edge predicates, the empty-fiber cases, and the universe level all agree
with the node and the source. I made no Lean or node changes. The node's dependency
records were usable as written: `EnhancedDiagramsCones` supplies mapping spaces and
coherent cones, `InfinityFibrations` supplies the two fibration predicates and fibers,
`InfinityMappingComposition` supplies the canonical composition package, and
`ModelInfinityDerivedAdjunction` supplies `CoherentAdjunction`.

Edge cases checked again: `E`, either fiber, or a mapping space may be empty; no
nonemptiness is inferred. Degenerate identity transports satisfy the endpoint and
triangle clauses. The `Fin 2` endpoints cover exactly 0 and 1, and `u` remains
arbitrary. The source's locally cartesian/cocartesian transport tests are rendered by
the imported `IsCartesianEdge`/`IsCocartesianEdge` predicates.

I searched Mathlib, the source `WeilConjectures` tree, and the project's `lean/Sheaf`
tree for the theorem and all helper names, and reran `msearch.py` LeanFinder, Loogle,
and grep searches. The only matching adjunction notion is the recorded
`CoherentAdjunction`; no interval bicartesian theorem or duplicate helper exists.
`scompile.py Q28 lem-coef-infinity-bicartesian-interval-adjunction` compiles the module
and its library form cleanly, with only the expected `sorry` declaration.

## Second reading by Q28

This is the fresh independent reading of the repaired delivery. I opened the current
item node, the sandbox module, all four statement-dependency node records and the
actual declarations in EnhancedDiagramsCones, InfinityFibrations,
InfinityMappingComposition, RightPinchComparison and ModelInfinityDerivedAdjunction.
There is no coord/repair-notes record for this item. The node has no statement_change;
its mathematical statement and seven proof steps agree with the current shared node.
The only node changes against that snapshot are lean and the addition of the already
recorded def-coef-coherent-adjunction-data to stmt_deps, as the maintainer requested.
There are no new nodes and no dependency modules in this delivery.

I read the online source places independently: [02FN](https://kerodon.net/tag/02FN),
[02FM](https://kerodon.net/tag/02FM), [019N](https://kerodon.net/tag/019N),
[01VN](https://kerodon.net/tag/01VN), [02EK](https://kerodon.net/tag/02EK),
and [02F1](https://kerodon.net/tag/02F1). These are Kerodon sources, not Stacks tags;
there is no corresponding Stacks tex source to open. The ambient objects are infinity
categories, with no finiteness, nonemptiness, coefficient, or model-category assumptions.
The transport definitions use locally cartesian edges, but the node explicitly uses
global cartesian edges. For a cartesian/cocartesian fibration over this interval the
transport tests agree; in particular the nondegenerate base-edge pullback is the total
space itself. The node's bicartesian-to-adjunction assertion agrees with 02FN.

Object, hypothesis and conclusion checklist, with the Lean rendering and verdict:

1. The small quasicategory E and simplicial map to the fixed interval are
   `{E : SSet.{u}} [Quasicategory E] (p : E ⟶ Δ[1])`. Verdict: exact. The two
   hypotheses `hp : cartesianFibration p` and `hq : cocartesianFibration p`
   use the recorded predicates, including inner horn lifting and lifts at every
   prescribed target/source. The standard interval instance is constructed from
   Mathlib's nerve instance; it is not an additional hypothesis.
2. The fibers E_0 and E_1 are `intervalFiber p 0` and `intervalFiber p 1`.
   The abbreviation unfolds to the recorded pullback `fiber`, and
   `intervalFiberInclusion` is its actual second projection. Verdict: exact strict
   fibers, with no arbitrary replacement categories or chosen inclusion maps.
3. The specified contravariant transport is the explicit input
   `R : intervalFiber p 1 ⟶ intervalFiber p 0`. Verdict: exact; R is not replaced
   by an existentially chosen right adjoint.
4. Its coherent witness is `h : Δ[1] ⊗ intervalFiber p 1 ⟶ E`.
   `h_over` is equality over the whole interval. `h_zero` is R followed by the
   zero-fiber inclusion, and `h_one` is the one-fiber inclusion.
   `intervalEndpoint` inserts the actual endpoint and identity on the other factor.
   Verdict: exact, including all simplices and the order of endpoints in 01VN.
5. `h_cartesian` quantifies over every vertex z of the one-fiber and tests
   `IsCartesianEdge p (lift (𝟙 Δ[1]) (SSet.const z) ≫ h)`.
   Verdict: exactly the required component edge, using the dependency's final
   outer-horn predicate rather than an ordinary categorical cartesian arrow.
6. The conclusion first existentially introduces
   `L : intervalFiber p 0 ⟶ intervalFiber p 1` and
   `k : Δ[1] ⊗ intervalFiber p 0 ⟶ E`. Its next four clauses give the over-base
   equation, zero endpoint inclusion, one endpoint L followed by inclusion, and
   `IsCocartesianEdge` for every vertex y. Verdict: exact, with the same
   quantifier order and the endpoint order of 019N.
7. `∃ adj : HomotopicalAlgebra.ModelInfinity.CoherentAdjunction L R` supplies the
   coherent adjunction of these very functors. I read the structure at lines 69–99:
   its unit and counit are edges of the full internal functor simplicial sets with
   endpoints id, RL and LR, id. Its left and right triangle fields give 2-simplices
   there, with successive edges Lη, εL and ηR, Rε, and degenerate identity long
   edges. Verdict: precisely 02EK's composition meaning, not objectwise triangle
   equations. Its universal unit/counit fields use the evaluated same edges and the
   actual coherent comma constructions. These express the natural represented
   mapping-space equivalences and introduce no model-category hypotheses.
8. `IntervalAdjunctEquivalences adj` supplies the explicit adjunct formula. Its
   `ηy.1 = (evaluation C C y).app _ adj.unitEdge` fixes the vertex to the unit's
   component. The tested map is `lift (mappingSpaceMap R (L.app _ y) z)
   (SSet.const ηy) ≫ c y (R.app _ (L.app _ y)) (R.app _ z)`.
   Verdict: exactly v ↦ R(v) composed with η_y, for every y and z, with equivalence
   interpreted by the recorded realization weak-equivalence predicate.
9. The composition representative c is fixed up to homotopy by the same degreewise
   rightPinchPrism formula, consecutive-edge and long-edge restrictions, inverse r,
   and composition homotopy as MappingCompositionStatement. Verdict: the canonical
   composition class, not an arbitrary operation. The unit and counit in the full
   internal homs and their universal comma objects retain coherent naturality in
   both variables. No strictly natural choice of representatives is imposed.

Edge cases: an empty total space and two empty fibers are allowed; no object is
chosen in the statement. Exactly one nonempty fiber is incompatible with one of the
prescribed lifting hypotheses, rather than excluded by a hidden Nonempty binder.
Empty mapping spaces are allowed, with the weak-equivalence component condition
still present. Identity transports and degenerate units/counits/triangles are covered.
The arbitrary universe u contains the total space, fibers and their internal homs;
there is no relation between independent universe levels and no unbound universe or
variable. The construction is simplicial in every degree including degree zero.
There is no scheme, coefficient ring, characteristic, zero object or integer degree
parameter whose edge cases could be silently restricted here.

Independent searches, using different wording from the worker:

- LeanFinder: “Simultaneous cartesian and cocartesian transport along the walking
  arrow gives left and right adjoints of quasicategories”. Eight hits, including
  nerveAdjunction and bicategorical Kan adjunction constructors. Their signatures
  concern nerve/homotopy-category functors or arbitrary bicategorical Kan extensions;
  none is the required interval-fibration theorem.
- Loogle: `"SSet", "Adjunction"`. Two hits: chainComplexFunctorAdjunction and
  sdExAdjunction. I opened their source declarations; they are ordinary adjunctions
  involving evaluation/chain complexes or subdivision/Ex and do not match.
- LeanSearch: “A fibration of infinity categories over the walking arrow with both
  cartesian and cocartesian lifts determines adjoint fiber transport functors”.
  Eight hits, all ordinary fibered-category lifting results or model fibrations;
  none states the quasicategorical transport adjunction.
- msearch grep `cartesian|cocartesian|adjoint` in AlgebraicTopology/Quasicategory:
  only the unrelated StrictBicategory future-work comment.
- Direct rg of Mathlib, upstream WeilConjectures and project lean/Sheaf for
  bicartesian fibrations, transport adjoints, the theorem and all helper names:
  no duplicate statement or helper. The upstream declaration census and upstream
  exact item-id search are empty. The existing CoherentAdjunction is reused.

Mismatch found and repaired: the module omitted two available proof-dependency
imports required by stages/2-statements.md §3(7): EnhancedFunctorConeCalculus and
SimplicialCompositionSpine. I added both as ordinary `import` lines and made the
EnhancedDiagramsCones statement dependency an explicit `public import`. A read-only
source import-closure traversal confirms neither proof import returns to this item.
No mathematical mismatch was found, and I changed no definition body or signature.
I verified the prior repair: the independent definition-node binding is used instead
of adding the downstream Quillen adjunction theorem as a DAG dependency, and the
main docstring now includes all seven current proof steps and their cited nodes.
Every helper has its source and blueprint docstring; no data is sorry. The sole
postponed proof is the public named bicartesian_interval_adjunction theorem.

Validation: scompile.py Q28 lem-coef-infinity-bicartesian-interval-adjunction compiled
the final module in both sandbox and library forms cleanly (1.4 s / 1.5 s), with no
warnings. Every Lean line is at most 100 characters; the node's lean.statement is
verbatim the file signature after the delivery reader's whitespace normalization.

## Maintainer review fix (2026-10-17)

Statement, definitions and node record unchanged. Following stages/2-statements.md §3(7),
added the non-public proof-dependency imports `Sheaf.CategoryTheory.RelativeConeEquivalence`
(lem-coef-infinity-relative-cone-equivalence, already landed in the delivery's base) and
`Sheaf.CategoryTheory.InfinityCocartesianMappingCriterion`
(lem-coef-infinity-cocartesian-mapping-criterion, landed on newtargets-dag at 09:10 on 2026-10-17).
Neither module reaches this item, so neither import closes a cycle. The remaining proof dependencies
(reflection-assembly, transport-uniqueness, adjunction-mapping-equivalence) have no Lean
record yet. Repaired one garbled citation in the worker report ("Kerodon Definition 6.2.1.1 (02EK)").
The per-file compile (nt_compile.py) of the fixed module is clean.
