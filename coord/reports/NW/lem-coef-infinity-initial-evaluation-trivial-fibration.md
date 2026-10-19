## Worker report

The module `lean/Sheaf/CategoryTheory/InitialEvaluationTrivialFibration.lean` states
`SSet.Enhanced.initialEvaluationTrivialKanFibration`, with `sorry` as its only proof.
No new definition, dependency module, or statement correction is needed.

Clause-by-clause correspondence:

- A fixed universe containing the simplicial sets is `{D B T : SSet.{u}}`, with
  `universe u` explicit and `autoImplicit false`.
- The quasicategory hypotheses are `[Quasicategory D] [Quasicategory B]
  [Quasicategory T]`.
- The maps are `(p : D ⟶ B) (q : T ⟶ B)` and the two left-fibration hypotheses
  are `(hp : leftFibration p) (hq : leftFibration q)`.
- The specified initial object is `(d : D _⦋0⦌) (hd : IsInitial D d)`.
- The base vertex `b = p(d)` is `p.app _ d`, and its strict target fiber is
  `fiber q (p.app _ d)`. The dependency's fiber convention is `{b} ×_B T`,
  canonically the node's `T ×_B {b}`.
- The relative internal functor simplicial set is expressed without a duplicate
  definition as `fiber ((ihom D).map q) (diagramVertex p)`.
  The existing internal hom has degree-n simplices `D × Δ[n] → T`.
  Postcomposition by `q` takes them to `D × Δ[n] → B`; the constant vertex
  `diagramVertex p` gives precisely `p pr_D`. Its strict fiber therefore imposes
  `qH = p pr_D` in every simplicial degree, with inherited restriction operators.
- The theorem supplies `ev` with the equation
  `ev ≫ pullback.snd ... q = pullback.snd ... ((ihom D).map q) ≫ evaluation D T d`.
  This requires exactly restriction of each relative diagram to `{d} × Δ[n]`.
  The other coordinate of the target fiber is the unique map to `Δ[0]`, so this
  equation uniquely determines `ev`. The existential is a characterization of
  the canonical restriction map, not an arbitrary map between these objects.
- `SSet.modelCategoryQuillen.I.rlp ev` asserts lifting against every boundary
  inclusion, including dimension zero. The latter boundary is empty by
  `SSet.boundary_zero`, so its lifting condition is surjectivity on vertices.
  This is exactly the dependency's recorded Mathlib match for trivial Kan
  fibrations; no extra Kan-Quillen weak-equivalence hypothesis is used.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsInitial`,
  `SSet.Enhanced.diagramVertex`, `SSet.Enhanced.evaluation`, and the reexported
  Mathlib `SSet`, `Quasicategory`, internal hom `ihom` and standard simplex.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, the recorded
  module of `def-coef-infinity-fibrations`, publicly reexports
  `Sheaf.CategoryTheory.InfinityFibrations`: its `SSet.Enhanced.leftFibration`
  is exactly the stated positive-dimensional initial-horn lifting predicate;
  `SSet.Enhanced.fiber` is the strict simplicial pullback.
- The Mathlib match for `def-weil-pbc-trivial-kan-fibration` is used directly:
  `SSet.modelCategoryQuillen.I`, `SSet.boundary`, `SSet.boundary_zero` and
  `CategoryTheory.MorphismProperty.rlp`. Their source signatures were read.
- The available proof dependencies are imported privately:
  `Sheaf.CategoryTheory.RelativeConeEquivalence`,
  `Sheaf.CategoryTheory.TerminalAnodyne`, and
  `Sheaf.CategoryTheory.RightFibrationExponentiation`.
  The theorem docstring carries all four DAG proof steps, including opposite
  mapping spaces, horn reversal, exponentiation, reversal of boundary lifts,
  and the strict pullback imposing the map `p`.

The source was read online: Kerodon Proposition the project server (038R), implication
(2) => (3), states evaluation for every left fibration over the same base, with
no initial object of its target required. The webpage was fetched read-only with
Python urllib after the web reader timed out. Its proof invokes Corollary
the project server and Proposition the project server, as does the DAG. A local archival copy remains
WANTED, as already recorded by the source field; none is added by this delivery.

Edge cases checked: dimension zero has an empty boundary and is included in `I`;
dimension one includes both endpoints; no nonemptiness of `T` or its fiber is
assumed. If `T` is empty then `D` is inhabited by `d`, so both the relative
functor set and the target fiber are empty and boundary lifting is vacuous.
An empty fiber over `p(d)` likewise forces the relative functor set to be empty
by restriction. An empty `D` is excluded exactly by the chosen vertex; an empty
base cannot receive it. No initial object of `T` is introduced. All simplicial
sets, internal homs and strict fibers remain in the freely chosen universe `u`.

Searches made on 2026-10-17:

- `msearch.py leanfinder`, query: "Evaluation at an initial object into a left
  fibration is a trivial Kan fibration on simplicial maps over a base".
  Eight hits concern ordinary fibrant objects or Kan-Quillen horn fibrations,
  not this specialized evaluation theorem.
- `msearch.py loogle`, query: `"LeftFibration"`. Zero hits.
- `msearch.py grep`, query:
  `left.?fibration|right.?fibration|initial.*evaluation|evaluation.*initial`.
  Four Mathlib hits concern ordinary augmented (co)simplicial-object evaluation.
- `rg` in the upstream `WeilConjectures/` tree for the item id and
  `left.?[Ff]ibration|initial.*[Ee]valuation|[Ee]valuation.*initial` found no hits.
- `rg` in `lean/Sheaf/` for evaluation at an initial object found the downstream
  `InitialLeftFibrationEquivalence` proof reference, but no duplicate theorem.
  The upstream name index contains no matching declaration.
- Project searches found `transportOverHom` in `SpaceTransportClassification`.
  That module's DAG proof closure reaches this item, so using it would create a
  cycle. The final statement instead uses the already available `fiber` and
  `ihom` constructions directly; no dependency on that module is delivered.

Validation: `scompile.py` compiles the final module cleanly, with only the expected
postponed theorem. The initial dry run found a cyclic added dependency and a
signature terminator mismatch; both were repaired. The final node changes only
`lean`, with the signature recorded up to (and excluding) `:=`.
No `STATEMENT-DISPUTED` issue was found.


## Second reading by NW

I independently read the node, Kerodon Proposition the project server (038R), and
`InitialEvaluationTrivialFibration.lean`. The Kerodon webpage was read using
Python urllib after the web reader timed out. Its opening hypotheses are a
left fibration of infinity categories and a specified object in its domain;
condition (2) makes that object initial, and condition (3) quantifies over
every target left fibration. This is precisely the node's specialization of
(2) => (3). No hypothesis is hidden in the surrounding source.

Object/hypothesis/conclusion checklist (every entry passes):

1. A fixed universe containing all three simplicial sets: `universe u` and
   `{D B T : SSet.{u}}`. There is no size inequality or extra equality.
2. Three quasicategories: `[Quasicategory D] [Quasicategory B]
   [Quasicategory T]`. These are exactly the source's infinity categories.
3. Left fibrations over the common base: `(p : D ⟶ B) (q : T ⟶ B)` and
   `(hp : leftFibration p) (hq : leftFibration q)`. I opened the recorded
   `InfinityFibrationsOverSimplicialBases` module and its public import
   `InfinityFibrations`: `leftFibration` quantifies over exactly the horns
   with `n ≥ 1` and `0 ≤ i < n`, without additional instances.
4. A specified initial object in D: `(d : D _⦋0⦌) (hd : IsInitial D d)`.
   I read `IsInitial`: every outgoing right-pinched mapping space is weakly
   contractible, as specified by `def-cbc-enhanced-diagrams-cones`.
5. The base vertex b = p(d) and strict target fiber: `p.app _ d` and
   `fiber q (p.app _ d)`. The dependency's real definition is the degreewise
   pullback of the constant point map and q, ordered `{b} ×_B T`; the two
   factor orders are canonically isomorphic and retain all simplices.
6. The relative functor simplicial set: the source of ev is
   `fiber ((ihom D).map q) (diagramVertex p)`. I read `diagramVertex` and the
   Mathlib internal hom implementation. Its n-simplices are precisely maps
   `D × Δ[n] ⟶ T` whose composite with q is p after projection to D. The
   fiber imposes this equality in every degree, with the inherited simplex
   restriction operators, as the node requires. No new copy is defined.
7. Evaluation by restriction at d: the existential `ev` satisfies the exact
   equation with `pullback.snd` and `evaluation D T d`. I opened `evaluation`:
   it is precomposition with the point of D followed by the internal hom unit
   isomorphism. The equation fixes its projection to T; its projection to
   Δ[0] is unique (`stdSimplex.ext₀`). Thus it uniquely determines the
   canonical evaluation, rather than allowing an arbitrary map.
8. Trivial Kan fibration, vertex surjectivity and all boundary lifts:
   `SSet.modelCategoryQuillen.I.rlp ev`. The dependency is a Mathlib leaf;
   I read its `mathlib_match`, `I := .ofHoms (fun n ↦ ∂Δ[n].ι)`, `rlp`,
   `boundary`, and `boundary_zero`. I also read Stacks `simplicial.tex`,
   Definition 08NL, lines 5533-5545. I contains every natural n, so n=0 is
   included and is exactly vertex surjectivity by the Yoneda bijection.
9. No initial object or nonemptiness of T or T_b: no such binder occurs.
   All objects are quantified before the asserted evaluation property, with
   the same order and scope as the node.

Edge cases: for empty T, D is inhabited by d and both the relative functor
simplicial set and the target fiber are empty; boundary lifting is vacuous.
An empty fiber likewise precludes a relative diagram by its evaluation at d.
Empty D and empty B are excluded exactly by the specified vertex and p, as
in the node. Dimension zero has empty boundary; dimension one retains both
endpoints. No field, characteristic, integer-degree, or zero-object parameter
occurs. Universe u is arbitrary and the internal hom and pullbacks stay in u.

Independent searches on 2026-10-17 (logged by msearch.py):

- LeanFinder: "Restriction of maps over a simplicial base to an initial
  vertex has the right lifting property against all simplex boundaries when
  the target is a left fibration". Eight hits give general Kan-Quillen
  generators/fibrations or Joyal lifting tricks; no evaluation theorem.
- LeanSearch: "The restriction of relative simplicial mapping objects to an
  initial vertex is a trivial Kan fibration for a left fibration". Eight hits
  concern relative morphisms, all-horn fibrations, interval inclusions or the
  initial simplicial set; none states this result.
- Loogle: `"IsInitial"` returned twelve Lean/ordinal declarations, no result.
  An earlier two-string query was rejected by the parser and was replaced
  by this successful query; its result is not evidence of a mathematical hit.
- grep service: `restrict.*initial|initial.*restrict|ev.*leftFibration|leftFibration.*ev`
  returned ordinary initial restriction of limits and order initial segments.
- Direct `rg` over Mathlib's simplicial-set sources, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for initial evaluation and the proposed declaration found no duplicate.
  Project hits concern based paths, ordinary limits or the downstream
  `InitialLeftFibrationEquivalence` proof reference. I read that theorem's
  signature; it asserts a quasi-inverse over B, not this evaluation result.

There are no new nodes, dependency modules, or statement corrections to audit.
I read the three available proof modules `RelativeConeEquivalence`,
`TerminalAnodyne`, and `RightFibrationExponentiation`; they are private proof
imports. The theorem docstring carries all four node proof steps: opposite
mapping spaces and terminal anodyneness, horn reversal and exponentiation,
internal-hom reversal and boundary lifts, and the strict pullback over p.
There are no definitions or hidden data choices in this delivery, and the
only proof is the named theorem's `sorry`. All variables and universes are
bound and all Lean lines are at most 100 characters.

No mathematical mismatch was found, and the Lean and node were left unchanged.
The second reading adds this report and removes its obsolete handoff sentence.
`lean.statement` is byte-for-byte the signature before `:=`; the node differs
from the repository copy only in `lean`. `scompile.py` compiled the sole
module cleanly with no warnings or errors. Final preflight and delivery are
performed using the prescribed deliver2.py wrapper.
