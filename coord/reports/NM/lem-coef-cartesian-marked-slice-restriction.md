## Worker report

The module `Sheaf/CategoryTheory/CartesianMarkedSliceRestriction.lean` states
HTT Proposition 3.1.1.11.  It uses the existing ordered join and join-slice
constructions and gives real postcomposition and restriction interfaces.  The
two existence-and-uniqueness statements only postpone the coherence proofs;
the definitions choose the uniquely specified maps, so no arbitrary map or
hollow data is introduced.  The final theorem has only `sorry` as its proof.

The Lean rendering of each clause is as follows.

* `E` and `B` are `SSet.{u}` with `[Quasicategory E]` and
  `[Quasicategory B]`; `p : E ⟶ B` and `hp : InnerFibration p` render the
  inner-fibration hypothesis.
* `U,V : Marked.{u}`, `i : U ⟶ V`, and
  `hi : Marked.markedAnodyne i` render the marked-anodyne inclusion.
* `q : V.underlying ⟶ E` is the marked diagram.  The hypothesis
  `hq : ∀ e, e ∈ V.marking → pCartesianEdge p (yonedaEquiv.symm (q.app _ e))`
  says exactly that every marked edge has a `p`-Cartesian image.
* `joinSlicePostcompose` is postcomposition by `p`.  `IsJoinSliceRestriction`
  records the degreewise formula that keeps the initial simplex and
  precomposes the ordered join with `(𝟙, i)`; its unique map is
  `joinSliceRestrict`.  `IsCartesianMarkedSliceRestrictionMap` records the two
  pullback projections, and `cartesianMarkedSliceRestrictionMap` is its unique
  canonical map.
* The conclusion
  `trivialKanFibration (cartesianMarkedSliceRestrictionMap p i q)` is the
  displayed restriction map and the source's trivial-Kan conclusion, including
  the dimension-zero vertex-surjectivity clause through the repaired
  `trivialKanFibration` definition.

Dependency declarations read in full:

* `SSet.Enhanced.cocartesianFibrationOver` and
  `SSet.Enhanced.IsCartesianEdge` from
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` and its public
  import `InfinityFibrations`.
* `SSet.Marked.marked_anodyne_lifting_calculus` from
  `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`.
* `SSet.Enhanced.trivialKanFibration` from
  `Sheaf.AlgebraicTopology.TrivialKanFibration`.
* `SSet.Enhanced.orderedJoinFunctor` from
  `Sheaf.AlgebraicTopology.PushoutJoinSaturation` and
  `SSet.Enhanced.joinSlice` from
  `Sheaf.CategoryTheory.JoinSliceRightFibration`.

Edge cases checked were `n = 0` (empty boundary and vertex surjectivity), empty
`U`, empty `V`, empty `L`, the identity inclusion, a fully marked simplex, a
minimal marking, degenerate marked edges, and `E` or `B` empty.  The ordered
join construction permits empty blocks and the join-slice data has no
nonemptiness hypothesis or smaller-universe restriction.

Searches made before writing:

* `msearch.py NM lem-coef-cartesian-marked-slice-restriction leanfinder`
  with the join-slice restriction description: no exact declaration; only
  generic quasicategory horn and model-category results.
* `msearch.py ... loogle 'orderedJoinFunctor, joinSlice, IsCartesianEdge'`:
  no Mathlib match; the canonical declarations are in the side modules above.
* `msearch.py ... grep 'marked.*anodyne|anodyne.*marked' AlgebraicTopology/`:
  no Mathlib match.
* During the repair self-check, `msearch.py ... leansearch 'Ordered simplicial
  join and join slices of diagrams into a simplicial set'` returned eight hits:
  `SSet`, `SimplicialObject`, `SSet.S`, `SimplicialThickening`, `SSet.hasColimits`,
  `SSet.hasLimits`, `SSet.Subcomplex.preimage_max`, and `SimplicialCategory`.
  None defines either requested notion. The full output is recorded in both
  new nodes. Repeated LeanFinder, Loogle and Mathlib grep searches for the
  relative marked-slice theorem again found no exact match.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` found the existing
  `orderedJoinFunctor`, `joinSlice`, `IsCartesianEdge`, and
  `markedAnodyne`; no standalone DAG records for ordered join or join slice.
  `tools/blueprint_refs.py search 'ordered join'` and `'join slice'` found no
  blueprint nodes.

No `STATEMENT-DISPUTED` flag or node fault remains.  The four delivered
dependency/new-node records are described below.

## New nodes

`def-coef-ordered-join` records the existing
`SSet.Enhanced.orderedJoinFunctor` as the canonical degreewise ordered join.
The three searches above found no Mathlib declaration or standalone DAG node;
the side declaration is exact.

`def-coef-join-slice` records the existing
`SSet.Enhanced.joinSlice`, whose stored `JoinSliceSimplex` contains precisely
the extension and initial-restriction equations in the node's displayed
degreewise slice.  The three searches found no Mathlib declaration or
standalone DAG node.

## Dependency modules

`def-coef-infinity-fibrations` had a Lean record for
`cocartesianFibrationOver` only, so it did not expose the node's required
Cartesian-edge predicate.  `InfinityFibrationsCartesianRepair.lean` states
`pCartesianEdge` exactly as the final-horn predicate, delegating to the
published `IsCartesianEdge`.

`def-weil-pbc-trivial-kan-fibration` had only a Mathlib match and no Lean
record.  `TrivialKanFibration.lean` states the source definition explicitly:
surjectivity on 0-simplices and boundary lifting for every positive dimension.

## Second reading by NM

I reopened the item and all four dependency records after compilation.  The
second reading checked each binder and conclusion against the node: the only
hypotheses are the two quasicategory instances, inner fibration, marked
anodyne map, and Cartesian marking condition; the conclusion is exactly the
canonical restriction map's trivial-Kan property.  The repaired dependency
modules state the recorded notions rather than stronger special cases, and the
new ordered-join and join-slice records point to their existing canonical
declarations. No mathematical mismatch was found. The repair self-check found
missing source/blueprint docstrings on the helper maps and predicates and an
incomplete construction proof description for the two unique-map theorems;
these are now supplied. The three files compiled cleanly in the initial
`deliver2.py --no-push` run through `scompile.py`; the expected theorem `sorry`
warning is disabled by the module option.

That dry run then reported five metadata faults: the two new nodes lacked
LeanSearch evidence, and their statements did not explicitly cite their three
listed dependency edges. It also diagnosed that the two existing-declaration
signatures must begin with `def` in the record. The repair records the actual
LeanSearch output, adds the dependency citations, and follows those exact
signature diagnostics. The item's statement and proof remain unchanged, and
comparison with the current shared node finds only `lean` and the added join
dependencies changed. Each repaired dependency differs only in `lean`.

This is the self-check of the retained stage-2 packet, not an independent
mathematical review; the maintainer performs that review. The repaired packet
is compiled and checked again before delivery.

## Maintainer review fix

The maintainer's reviewer (cc review service) replaced the item module and
left out both dependency-module changes (`--revert-nodes
def-coef-infinity-fibrations,def-weil-pbc-trivial-kan-fibration`), under
delivery-errors H4/H13: both dependency notions were already usable.

* `def-weil-pbc-trivial-kan-fibration` carries the Mathlib match
  `SSet.modelCategoryQuillen.I.rlp` (boundary inclusions `∂Δ[n].ι` for all
  `n ≥ 0`; `∂Δ[0] = ∅` gives vertex surjectivity), which 29 landed project
  modules already use.  The new `SSet.Enhanced.trivialKanFibration` was a
  second definition of that notion.  The conclusion is now
  `SSet.modelCategoryQuillen.I.rlp (cartesianMarkedSliceRestrictionMap p i q)`.
* `def-coef-infinity-fibrations`: its recorded module
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases` publicly
  re-exports `Sheaf.CategoryTheory.InfinityFibrations`, where
  `SSet.Enhanced.IsCartesianEdge` (blueprint: def-coef-infinity-fibrations) is
  exactly the node's final-horn p-Cartesian predicate.  The wrapper
  `pCartesianEdge` was a duplicate, and its record would have replaced the
  node's landed `cocartesianFibrationOver` record.  The hypothesis `hq` now
  uses `IsCartesianEdge` directly.

Nothing else changed: the helper maps, the hypotheses and the new nodes
`def-coef-ordered-join` and `def-coef-join-slice` are as delivered.  The fixed
module compiles cleanly per file through `tools/nt_compile.py`.

