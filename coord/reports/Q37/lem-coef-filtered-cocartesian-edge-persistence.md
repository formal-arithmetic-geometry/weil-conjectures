## Worker report

The module `Sheaf.CategoryTheory.FilteredCocartesianEdgePersistence` states
`SSet.Enhanced.FilteredCocartesianPersistence.filtered_cocartesian_edge_persistence`
with `sorry`. Its three helpers bundle the supplied diagram and spell out the canonical
relative precomposition roof. There are no postponed construction proofs, new independent
notions, dependency replacements or statement corrections. The landed shared compilation
repair described below is reused.

Source read: Gepner--Haugseng, *Enriched infinity categories via nonsymmetric infinity
operads*, https://arxiv.org/html/1312.3178v4, Proposition 3.3.2, especially the proof of
(ii). The DAG extracts the argument for the one selected edge rather than requiring
lifts for all objects over one base arrow. The four proof steps in the node are carried
in the theorem docstring; no proof is attempted at stage 2.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small universe is `u`. The existing `CatInfinity.{u}` lives in `u + 1` and its
  vertices encode actual `u`-small quasicategories. `Data.b` encodes the arbitrary small
  base `B`; `catInfinityObject data.b` is that base, including the empty quasicategory.
- The small filtered infinity category is `Data.I : SSet.{u + 1}`, with its explicitly
  bound `Quasicategory` instance, `Presentability.IsSmall.{u, u + 1}`, and
  `Presentability.IsKappaFiltered Cardinal.aleph0`. This tests all finite coherent
  diagrams, including the empty diagram. No ordinary-category index is substituted.
- The coherent slice diagram is `Data.diagram : I ⟶ rightVertexSlice CatInfinity b`.
  This is the already defined join slice, not a strict ordinary over-category. Its
  simplices retain the structural triangles and all their higher compatibilities.
- The structural functors `p_j` are `Data.pStage j`, normalized by
  `pStage_normalized` to `catInfinityArrow (diagram.app _ j).val`. These heterogeneous
  equalities identify the actual endpoint types of the decoded arrow; they add no
  strict commutation requirement on transition functors over the base.
- The supplied cocone is `Data.cocone`, with `slice_colimiting` exactly its colimiting
  property in the infinity slice. `total_colimiting` applies `IsColimiting` to its
  actual `Spaces.mappedCocone` under `rightVertexSliceProjection`; it uses the entire
  underlying cocone, not merely a different cocone on an equivalent apex.
- Its structure functor `p` is `Data.p`, normalized by `p_normalized` to the actual
  structure edge of the slice apex. The cocone legs `r_j` are `Data.leg j`.
  `leg_normalized` identifies each with `catInfinityArrow` of evaluation at `j` of
  the complete underlying `CatInfinityCalculus.coconeArrow`. They are the given legs,
  with their actual endpoint transports, rather than arbitrary functors.
- The fixed stage is `Data.i`. The theorem's `e : Δ[1] ⟶ ...` is an arbitrary edge
  of its stage category; its source and target are not restricted or separately chosen.
- For every `j` and `a : I.Edge i j`, `Data.transition j a` is normalized to the
  functor decoded from the projected diagram edge by `transition_normalized`.
  The theorem's `stageCocartesian` says exactly
  `CocartesianStraightening.IsIntrinsicEdge (pStage j) (e ≫ transition j a)`.
  Objects of the coherent coslice `I_{i/}` are precisely these edges; their higher
  coherence is retained in the original diagram. Identity edges are included.
- The first conclusion is the recorded intrinsic predicate
  `CocartesianStraightening.IsIntrinsicEdge data.p (e ≫ data.leg data.i)`.
- The second conclusion quantifies over every object `z` of the actual apex category.
  Its arrow-space vertex `s` is constrained by
  `(arrowMappingSpaceInclusion _ x y).app _ s = diagramVertex (e ≫ leg i)`.
  Since this is the inclusion of the fixed-endpoint arrow fiber, that equality forces
  `x` and `y` to be the actual source and target of the image edge. They cannot be
  unrelated objects chosen to weaken the conclusion.
- `RelativePrecompositionAt p x y z s` expands the relative equivalence. The existing
  `cocartesianPrecompositionSource` is the canonical triangle roof for composing `s`.
  Its second projection is `precompositionProjection`; its long-edge restriction is
  the existing `cocartesianPrecomposition`. Both are actual constructions.
- The map `q` between triangle roofs is fixed on entire triangles by its equation with
  `cocartesianPrecompositionInclusion` and `(ihom Δ[2]).map p`. Thus neither it nor the
  induced relative maps are arbitrary comparisons. `wLeft` and `wRight` are precisely
  their strictly commuting squares with the two restrictions.
- For EVERY base arrow `g` in `arrowMappingSpace B (p y) (p z)`, the predicate supplies
  a base triangle `beta` with first edge `p(s)` and second edge `g`. The long edge
  therefore represents `g p(s)`. This chooses a composition witness in the base, not a
  lift to `E`. All composites in a quasicategory have such triangle witnesses.
- The two `HomotopySegal.fiberMap` expressions form the specified precomposition span:
  `Map^g_E(y,z) ← hofib_beta(q) → Map^(g p(s))_E(x,z)`. The left map forgets the
  composition triangle and is the canonical triangle-roof equivalence. The right map
  restricts to the long edge. Each map applies the actual total-space map to its first
  coordinate and the actual base map to its path coordinate. Both are asserted weak
  homotopy equivalences, giving exactly the equivalence induced by precomposition.
  The arrow-space model is the existing model used by `IsIntrinsicEdge`; the recorded
  right-pinch comparison identifies it with the node's mapping spaces. Homotopy fibers
  are the same recorded path-model `Enhanced.homotopyFiber`, not ordinary fibers.
- No other cocartesian lifts, fibration hypothesis on any `p_j` or `p`, full faithfulness
  of a transition, or lifting assumption for `g` occurs anywhere in `Data` or the theorem.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.coconeCategory`,
  `IsColimiting`, `diagramVertex`, `evaluation`, `homotopyFiber`,
  `IsWeakHomotopyEquivalence`. Their full signatures and docstrings were read.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `SSet.Presentability.IsSmall`
  and `IsKappaFiltered`, with the small/ambient universes explicit.
- `Sheaf.CategoryTheory.CocartesianStraightening`:
  `SSet.Enhanced.CocartesianStraightening.IsIntrinsicEdge`; read its complete mapping
  square and its canonical triangle normalization. The recorded module also exposes
  the actual `CatInfinity`, `catInfinityObject`, `catInfinityArrow`, and the join slice
  through `CompleteAlgebroid` / `CatInfinityOppositeInvolution` / `SliceArrowEquivalence`.
- `Sheaf.CategoryTheory.CatInfinityFilteredFiniteCalculus`:
  `SSet.CatInfinityCalculus.coconeArrow`; this is generic in the actual coherent target,
  unlike that module's `coconeLeg`, which is specialized to its marked-model nerve.
  This already landed node is added to `stmt_deps` because its helper occurs in `Data`.
- `Sheaf.CategoryTheory.HomotopySegalSpace`: `SSet.HomotopySegal.fiberMap`, including
  the full construction and the domain/base square equations. Its already landed
  owning node `def-coef-homotopy-segal-space` is added to `stmt_deps`; no second generic
  fiber-map construction was introduced.
- The modules of stated proof dependencies are imported: `EnhancedFunctorConeCalculus`,
  `InfinityHomBifunctorFunctoriality`, `SpacesHomotopyFiberDetection`, plus the public
  dependencies above. `lem-coef-spaces-small-colimits-universe` has no recorded Lean
  declaration/module at this base, so there is no module for that proof dependency to
  import. It is a proof prerequisite, not a missing notion needed for this statement.

Edge cases checked before writing and again against the final file:

- The empty index is excluded exactly by the empty-diagram part of filteredness; the
  fixed stage also witnesses nonemptiness. No unnecessary `[Nonempty]` is assumed.
- Empty total or stage categories have no specified `e`; this is the correct vacuity.
  Empty base categories remain allowed in `Data`, with the same vacuity when `e` is fixed.
- Empty base mapping spaces make the `∀ g` clause vacuous, as in the node. Nonempty base
  mapping spaces with empty relative mapping fibers are covered by weak equivalences
  of the actual path-model fibers; no point of either relative space is assumed.
- Degenerate `e`, identity transitions, identity base arrows and arbitrary noninvertible
  base arrows are all included. `beta` is only a composition triangle in the base.
- Non-fully-faithful transitions and functors without any other cocartesian lifts are
  admitted. The intrinsic predicate does not require inner fibrations.
- The larger simplicial presentation of a small index is allowed by `IsSmall`; there
  is no accidental equality of the small and ambient universe.

Searches for an exact existing theorem / reusable notions (2026-10-17):

- `msearch.py ... leanfinder` with “In a filtered colimit of infinity categories over a
  base, an edge all of whose transition images are cocartesian remains cocartesian”:
  8 hits, all ordinary `Functor.IsCocartesian` / `IsStronglyCocartesian` lemmas. No match.
- `msearch.py ... loogle 'CategoryTheory.Functor.IsCocartesian'`: 12 ordinary-category
  hits. Read `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean` signatures and
  docstrings: ordinary unique lifting, not equivalences of infinity mapping spaces.
- `msearch.py ... leansearch` with “Cocartesian edges persist in filtered colimits of
  infinity categories over a fixed base”: 8 generic ordinary filtered-colimit and
  stability hits, no exact theorem.
- `msearch.py ... grep 'cocartesian|filtered.*colimit' CategoryTheory/FiberedCategory`:
  six ordinary cartesian/cocartesian source hits; no infinity persistence statement.
- `msearch.py ... grep 'quasicategor|cocartesian.*[Cc]olimit'
  AlgebraicTopology/Quasicategory`: strict bicategory and ordinary-nerve infrastructure,
  not the requested coherent slice-colimit result.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` with
  `cocartesian.*colimit|filtered.*cocartesian|lem-coef-filtered-cocartesian-edge-persistence`:
  no exact existing theorem; side hits include separate cocartesian-section results.
  The exact item-id search in upstream sources has no hit.
- Searched `dag/lean_names_upstream.json` for `cocartesian|Cocartesian|filtered`: only
  unrelated ordinary-category/étale/module filtered-colimit declarations.
- Read `FilteredFiniteRelativeConePersistence.lean` as an adjacent example; its relative
  limit-cone theorem is not this cocartesian-edge theorem. Read the existing right-join
  slice, arrow-space/triangle-roof definitions, and generic fiber map and reused them.

Validation: the final module was compiled by the prescribed `scompile.py Q37
lem-coef-filtered-cocartesian-edge-persistence <file>` wrapper in both its scratch
module and final library module paths, cleanly in 2.4/2.8 seconds. An initial unresolved
projection elaboration was repaired by the typed actual `precompositionProjection`;
a line-width warning was repaired. No warnings remain. The only theorem proof is `sorry`.

## Second reading by Q37

Author's second pass, with the node and final module open; the dispatcher forbids starting
other agents and the maintainer supplies the independent mathematical reading. I checked
all fields of `Data` against the quantifiers above: the slice and total colimit are both
present; stage and leg functors are normalized to the actual coherent diagram; all arrows
out of the fixed stage, including identities, occur in `stageCocartesian`. The first
conclusion is exactly the dependency's intrinsic edge predicate.

I then expanded the relative clause. It quantifies over arbitrary `z` and `g`, not merely
arrows that lift, and the point `beta` specifies composition in the base only. The left
fiber map forgets a triangle and the right restricts its long edge, so their span gives
precomposition on precisely the two stated homotopy fibers. The inclusion equation for
`s` fixes both endpoints and the image edge. The equation fixing `q` is on entire
triangles and hence prevents an arbitrary map from replacing the canonical operation.
The weak equivalence of the left fiber map is the standard contractible triangle-choice
comparison; it adds no mathematical hypothesis. I checked empty fibers and the identity
cases explicitly. No statement mismatch or disputed case remains. This pass retained the
node's natural statement and proof unchanged and retained the two landed helper owners
in `stmt_deps`. The repair also adds the transitive SpaceValuedStraightening owner. The module, declaration list and verbatim theorem signature were checked
against the node's `lean` record.

## Shared dependency repair

The first saved-packet dry run exposed `SpaceValuedStraightening.lean:64:7`,
`lean.dependsOnNoncomputable`: the recorded `Diagrams` abbreviation used the newly
noncomputable `smallSpaces` without its required modifier. I read the server source with
`scompile.py --source`, prepared the §1(B) repair `noncomputable abbrev Diagrams` in the
sandbox, and validated it with the item using the prescribed two-file `scompile.py`.
Both modules compiled without errors or warnings. Repaired dry runs also passed, including
`9d9a398e75` and `0d7e0a077d`.

Before final delivery, another group landed that same repair. I confirmed the current
server source with `scompile.py --source Sheaf.CategoryTheory.SpaceValuedStraightening`:
`Diagrams` now has exactly the required noncomputable marker and the same data. The current
record's `lean.note` explains that repair. This packet therefore uses the landed module
and removes the redundant dependency module and dependency node record. The item imports
`Sheaf.CategoryTheory.SpaceValuedStraightening` explicitly and adds its existing owner
`lem-coef-space-valued-straightening` to `stmt_deps`. No dependency node is re-recorded.
Its 655-node statement/proof prerequisite closure does not reach this item.

## Repair self-check (2026-10-17)

The returned `--apply-fixes` diagnostic concerned the maintainer fix-packet report path.
This repair uses the prescribed worker packet `report.md`; the delivery wrapper stages
it at `coord/reports/Q37/lem-coef-filtered-cocartesian-edge-persistence.md` and accepted
that shape in its successful dry runs. No maintainer tool or live file was edited.

I reread the retained item node and module. All fields of `Data`, the intrinsic-edge
conclusion and the relative triangle-roof conclusion have the clause correspondence
recorded above. The natural statement, proof and proof dependencies are unchanged.
The item source changes only by explicitly importing the now-repaired landed dependency;
its theorem signature is verbatim in `lean.statement`, and all lines are at most 100
characters. Universes and variables are explicitly bound; all definitions have real data;
the single postponed theorem retains its complete four-step proof docstring and `sorry`.
The final packet contains exactly the item module, item node and this report. No new node,
statement correction, disputed statement or dependency replacement is delivered.

The final dry run and push repeat preflight and per-file compilation against the current
shared branch, using the landed dependency repair.
