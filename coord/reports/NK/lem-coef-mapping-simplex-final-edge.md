## Worker report

The module [MappingSimplexFinalEdge.lean](lean/Sheaf/CategoryTheory/MappingSimplexFinalEdge.lean) defines the finite-chain presentation data, its simplex degree formula, vertices, final edge data, and states `CategoryTheory.mappingSimplex_final_edge` with proof `sorry`. The theorem has `n > 0`; a final vertex `y`; the penultimate index `iPrev` with `iPrev.val + 1 = n`; the transported vertex `y'`; an incoming vertex `x` represented by an index `i < n` and vertex `a`; and concludes that composition with the final edge is a weak homotopy equivalence of enhanced mapping spaces. The five proof clauses are recorded in the declaration docstring: factorization, inner-anodyne filtration, interval pushout comparison, explicit mixed mapping calculation, and two-out-of-three transport.

The module imports `Sheaf.CategoryTheory.EnhancedDiagramsCones` for `SSet.Enhanced.IsWeakHomotopyEquivalence` and mapping spaces, and `Sheaf.CategoryTheory.CoherentNerveComparison` for the coherent nerve framework. The dependency nodes used are `def-cbc-enhanced-diagrams-cones` (`SSet.Enhanced` constructions) and `lem-coef-coherent-nerve-comparison` (coherent realization context).

Edge cases checked include `n = 1`, where `iPrev = 0` and the final edge is the unique transition edge; empty fibres (the universal statement remains conditional on supplied vertices); and disconnected fibres (no connectedness or fibrancy hypothesis is added). No quasicategory or fibration assumption appears.

Searches recorded on the node were rerun: LeanFinder semantic searches for final-edge mapping-simplex composition and coherent-realization mapping spaces (only ordinary nerve/model-category hits); Loogle searches for `"SSet", "mapping"` and `"SSet", "sHomComp"` (no match); grep over Mathlib AlgebraicTopology for `mapping.?simplex|CartesianFibration|rigidification` (no match); and project grep for the item id (no existing declaration). The existing enhanced-diagram and coherent-nerve declarations were read in full and reused.


## Second reading by NK

I independently read the item node, the proposed module, the two recorded dependency
nodes and their Lean declarations, and HTT Lemma the project server, printed pp. 182--183
(PDF pp. 199--200). The node cites HTT, not a Stacks tag; no Stacks hypothesis is
applicable. The lemma explicitly assumes arbitrary simplicial sets and positive
chain length. Its earlier mapping-simplex definition and Notation the project server fix the
operators and edge. The node agrees with this source. No natural-language statement
correction was needed; there are no new nodes or dependency-module deliveries.
The first worker's description above is retained as history and is superseded by
the following reading of the repaired file.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Small simplicial sets, standard simplices and weak homotopy equivalences:
   `SimplexChain.{u}` takes values in `SSet.{u}` for arbitrary `u`.
   `SSet.Enhanced.IsWeakHomotopyEquivalence` is the recorded dependency definition:
   bijection on path components of realization and bijections on all positive based
   homotopy groups, at every source base point. Verdict: exact; no Kan condition.
2. Coherent realization and its enriched mapping sets:
   `R : CoherentNerveComparisonStatement.{u}` is the supplied, existing realization
   framework, not a new definition or an extra fibrancy condition. Its
   `rigidification : SSet.{u} ⥤ SCat.{u}`, `adjunction`, `simplex_realization`,
   `simplex_maps` and `colimit_extension` specify the simplex-colimit realization and
   the coherent nerve. Its existence is the recorded theorem
   `CategoryTheory.coherent_nerve_comparison : Nonempty CoherentNerveComparisonStatement`.
   Quantifying the supplied framework keeps the statement valid for every such
   normalized realization and avoids choosing data from that mere existence theorem.
   Verdict: same coherent realization, with its actual enriched homs.
3. Positive chain length: the dimension is `n + 1`, with `n : ℕ`; every positive
   integer is uniquely of this form. Verdict: exactly the source's `n > 0`.
4. Chain `A_0 <- ... <- A_last`: `A : SimplexChain.{u} (n + 1)` is the existing
   abbreviation `(Fin (n + 2))ᵒᵖ ⥤ SSet.{u}`. I read its declaration in
   `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`, including
   `MappingSimplexDegree`, `mappingSimplexOperator`, `mappingSimplexOperator_laws`,
   `mappingSimplex` and `mappingSimplexFiberInclusion`. A functor supplies all chain
   composites and their laws and imposes no property on its maps. Verdict: exact.
5. Mapping simplex, including operators: `mappingSimplex A` has the actual dependent
   pair of a monotone base map and a simplex of its last fibre. Its operator first
   applies the fibre restriction and then the chain map from the old last index to
   the restricted last index. Its functor-law proofs refer to the existing named
   well-definedness theorem. Verdict: exactly the node's degree formula AND operators;
   an arbitrary degreewise bijection would not suffice.
6. Final vertex: `y : (A.obj (op (Fin.last (n + 1)))) _⦋0⦌`.
   Verdict: every final-fibre vertex, no additional choice or hypothesis.
7. Penultimate image `y'` and the specific final edge: `mappingSimplexFinalEdge A y`
   is the dependent pair with base map `j ↦ n + j.val` from `[1]` to `[n + 1]`
   and fibre edge `(A.obj (op (Fin.last (n + 1)))).σ 0 y`.
   Its endpoints under the EXISTING operator formula are, respectively, the vertex
   `(n,t_{n+1,n}(y))` and `(n+1,y)`: at the initial face the operator uses the last
   transition, and at the final face it uses the identity transition. Thus `y'` is
   determined, not separately assumed. Verdict: the specified final edge itself.
8. Incoming vertex over an earlier index: `x : (mappingSimplex A) _⦋0⦌` and
   `hx : x.1 0 < Fin.last (n + 1)`. Since a zero-simplex base map has domain `Fin 1`,
   its value at `0` is its unique base vertex. Verdict: every and only allowed `x`,
   including vertices in the penultimate fibre.
9. Realized objects and edge: `R.adjunction.unit.app (mappingSimplex A)` is the
   canonical map `M -> N_hc(R.rigidification.obj M)`. Its image of `x`, evaluated on
   the sole thickened zero-simplex object, is the object used as source. Its image
   of `mappingSimplexFinalEdge A y` is the corresponding enriched interval functor.
   `coherentNerveIntervalArrow` evaluates this functor's enriched map on the constant
   zero-simplex at the full path `{0,1}` and applies Mathlib's `homEquiv'` inverse.
   Naturality at the two face maps identifies its two object values with the unit
   images of the two endpoints in item 7. Verdict: precisely `[e] : y' -> y`.
10. Composition and conclusion: Mathlib's `eHomWhiskerLeft SSet` postcomposes enriched
    homs with that actual arrow. Its domain is `C[M](x,y')` and its codomain is
    `C[M](x,y)`; both use the same realized source from item 9. Inspection of
    `CategoryTheory.Enriched.Ordinary.Basic` shows this is the right-unitor inverse,
    tensor with the arrow's unit map, and enriched composition. The conclusion is
    exactly `IsWeakHomotopyEquivalence` of this map. Verdict: exact source, target,
    direction, map and weak-equivalence condition; no endomorphism substituted.
11. No quasicategory or fibration hypothesis: there are no such binders on the
    fibres or on `M`. The supplied realization framework applies to every simplicial
    set. Verdict: the explicit last sentence of the node is respected.

Mismatches found and repaired:

- H3/H4: `MappingSimplexPresentation` supplied arbitrary `M` and unconstrained
  degreewise equivalences; it did not constrain any simplicial operator. Removed
  this private second construction and reused the already landed canonical
  `SSet.Enhanced.mappingSimplex` and functor-valued chains.
- H3: the unused `finalEdge` field had no relation to `y`, `y'` or the map. Replaced
  it by the explicit final interval and the degeneracy of `y`.
- H3: `P.composition` was arbitrary and was an endomorphism with target `y'`.
  Replaced it by Mathlib's enriched postcomposition to the final vertex `y`.
- H3: `SSet.Enhanced.mappingSpace M` is the right-pinched mapping simplicial set of
  `M`, not the enriched hom of its coherent realization. Removed that substitution;
  the repaired map uses enriched homs in `R.rigidification.obj M` directly.
- H8/H9: the structure and vertex helper lacked source/blueprint docstrings, and
  the file had no required module docstring. Replaced the obsolete declarations,
  supplied all source/blueprint docstrings and a module header, and expanded the
  theorem's five proof steps with their cited nodes and the actual pushout and
  two-out-of-three maps. The signature now contains no hidden `show` proof.
- Added the already stated proof-dependency imports for coherent inner anodyne
  equivalences, Joyal homotopy exponentials and the Joyal model structure.
  The remaining proof dependencies have no recorded module at this reading.
- Updated `lean.declarations` and copied `lean.statement` verbatim from the repaired
  theorem signature. No field of the natural statement, proof or dependencies was
  changed.

Reuse and import direction: the canonical mapping-simplex definitions already live
in the broader Cartesian presentation theorem module. Importing that module reuses
its construction; it does NOT assume its presentation theorem as a mathematical
prerequisite, so no dependency on that downstream theorem was added to the DAG.
Its reverse proof import of the present final-edge module must be omitted under
stages/2-statements.md §3(7), because it would close the two-module import cycle.
This is preferable to copying the existing construction. No existing public module
or dependency record was edited. The generic interval-arrow helper is an explicit
piece of this item's canonical map, not another realization or another definition
of weak equivalence.

Edge cases: original dimension one is `n = 0`, where the base edge is exactly
`0 -> 1`, the source restriction is `x` in fibre zero, and the final transition is
`A_1 -> A_0`. Original dimension zero is excluded by the node and cannot be supplied.
Empty fibres and empty mapping sets are allowed; `y` and `x` are universally bound
actual vertices, so an empty relevant fibre gives a vacuous instance rather than a
nonemptiness assumption. No connectedness, local Kan, or fibration constraint is
present. Arbitrary simplicial degeneracies and noninjective transitions remain
allowed. There is one arbitrary universe `u` for small simplicial sets and the
framework's small enriched categories; `Fin` and its `ULift` in the coherent nerve
work at every such universe. Schemes, rings, characteristic and a separate zero
object play no role in this simplicial statement.

Independent searches (different semantic queries from the first worker):

- `msearch.py ... leansearch "Coherent realization postcomposition with mapping
  cylinder transition is a weak equivalence"`: eight generic model-category
  postcomposition/cylinder hits; none states this mapping-simplex result.
- `msearch.py ... leanfinder "Rigidification mapping simplicial set of a mapping
  simplex final transition edge"`: eight horn/edge/spine hits; none is this result.
- `msearch.py ... loogle '"sHomComp"'`: only the definition of enriched composition.
  I opened `SimplicialCategory/Basic.lean` and then the enriched whiskering definitions;
  they provide the composition operation, not the asserted equivalence.
- `msearch.py ... grep 'mapping.?simplex|coherentNerveIntervalArrow|mappingSimplex_final_edge'
  AlgebraicTopology`: no Mathlib match. Direct `rg` searches for mapping simplex,
  mapping cylinder and rigidification throughout upstream `WeilConjectures` found
  only unrelated algebraic-geometric rigidifications, not this construction/result.
- `rg` in project `lean/Sheaf` and the DAG found the canonical `SimplexChain`,
  `mappingSimplex` and its operators in the Cartesian presentation module; these are
  reused. `MappingSimplexConeFibers` also uses that same construction. I also opened
  `PinchedRigidificationResolution` to check the existing explicit realization and
  vertex construction; no duplicate rigidification is introduced here.
- Searches for `FinalEdge`, `final_edge`, `IntervalArrow`, `mappingSimplexFinal` in
  Mathlib, upstream, project Lean and `dag/lean_names_upstream.json` found no matching
  declaration. `RelativeColimitFinalEdge` is a different limit-comparison predicate.
  Project interval-edge readers in `SpaceTransportClassification` specialize to
  spaces or `CatInfinity`; they do not give the general SCat arrow reader used here.

Validation: the repaired module compiled cleanly through the prescribed
`scompile.py NK lem-coef-mapping-simplex-final-edge <file>` in both sandbox and
library checks (1.6 seconds each), with no errors or warnings. All variables and
universes are bound, all lines are at most 100 characters, the two helper definitions
contain actual data, and the only theorem proof is `sorry`.
