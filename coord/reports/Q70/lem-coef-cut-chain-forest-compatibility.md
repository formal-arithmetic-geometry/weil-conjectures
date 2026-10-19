## Worker report

The module `lean/Sheaf/CategoryTheory/CutChainForestCompatibility.lean` states the
node's finite ordered Cut-chain forest compatibility theorem.  It introduces the
concrete finite data needed to render every object in the statement: `Layer`,
`identityLayer`, `substitute`, `cutLayer`, `Chain`, `width`, `oppositeMap`, `Forest`,
`fullRecord`, `Tree`, `Tree.leaves`, `Tree.graft`, `nextTrees`, `runTrees`,
`Forest.trees`, `Forest.widthAt`, `Forest.discarded`, `Forest.prefix`, `Forest.suffix`,
`Forest.discardedTrees`, `Forest.collapse`, `Forest.restrict`, and `restrictChain`.
The `Compatible` proposition is the clause-by-clause Lean rendering, and the only
proof is the required `sorry` in `cutChain_forest_compatibility`.

The node's single statement dependency is `def-weil-pbc-simplicial-set`.  It is a
Mathlib leaf (`SSet` and the related simplicial-set API), so no dependency module is
needed.  The module uses Mathlib's `SimplexCategory`, `SimplexCategory.Hom`,
`Fin`, `List`, and `SSet` definitions directly; it does not copy the simplicial-set
notion.

The first paragraph of the node is rendered by `cutLayer`: opposite monotone maps
are represented by `SimplexCategory` morphisms and each output fibre is the filtered,
increasing list of input labels.  `substitute` is ordered concatenation of earlier
fibres, with absent indices mapped to the empty list, so composition includes inputs
sent to the basepoint and empty fibres.  `identityLayer` gives singleton corollas.
`Chain`, `width`, and `oppositeMap` introduce the finite simplex chain and its
opposite maps.

The full forest record paragraph is rendered by `Forest`, `fullRecord`, and the
`Tree`/`runTrees` definitions.  Every output corolla is retained by `nextTrees`,
including a nullary corolla; `Tree.wire` labels initial wires and `Tree.node` stores
stage, output label, and ordered child trees.  `Forest.trees` computes all final
output trees.  `Forest.discarded`, `prefix`, `suffix`, and `discardedTrees` retain
unused wires and components in the full record.

The external interval clause is the `external_interval` field of `Compatible`.
Its `cutLayer (oppositeMap σ 0 (Fin.last q) ...)` is the composite interval, and
`Tree.leaves` records the increasing initial-wire labels, while `getD []` handles
an empty fibre.  The splitting and ordered grafting clauses are respectively
`Compatible.splitting_grafting` and `Compatible.ordered_leaf_concatenation`, using
`Forest.prefix`, `Forest.suffix`, and `Tree.graft`; the latter recursively replaces
wire slots by the corresponding earlier tree and preserves nullary nodes.

The restriction paragraph is rendered by `Forest.collapse`, `Forest.restrict`, and
`restrictChain`.  `collapse` folds `substitute` over all intervening layers, with an
empty segment starting from singleton identities.  `Compatible.restricted_record`
asserts equality of the restricted chain's full record and this operation;
`repeated_stage_identity` states the singleton identity layer for equal retained
stages.  `successive_restrictions` states functorial composition of restrictions,
and `restriction_grafting` states grafting compatibility after every restriction.
The final theorem has exactly the node's arbitrary-chain quantifier and all seven
compatibility fields; it asserts no target-category coherence.

Edge cases checked before writing and in the definitions include `q = 0` (the
`Fin q` layer list is empty and the selected tree is an initial wire), `p = 0` and
`r = 0` restrictions, repeated stages (`θ k.castSucc = θ k.succ`), zero ordinals
(empty corolla lists), empty input fibres (nullary nodes), wires sent to the
basepoint (retained by `discarded`), and empty list lookups (`getD`).  The endpoint
map proofs use `Fin.castSucc_le_succ` and `Fin.zero_le`, so no positive-size
assumption is imposed.

Searches made for an existing notion or theorem:

* `msearch.py Q70 ... grep "Cut|planar.*forest|corolla|graft" AlgebraicTopology` found only generic model-category/quasicategory files and no ordered Cut forest.
* `msearch.py Q70 ... loogle "SimplexCategory.Hom, SimplexCategory.Hom"` returned only ordinary simplex morphism declarations (`SimplexCategory.Hom`, `.id`, `.comp`, `.mk`, and related API), not this theorem.
* `msearch.py Q70 ... leanfinder "Cut functor opposite simplex category ordered finite forests compatible restriction grafting empty fibres"` returned generic simplex and simplicial-object declarations, not this notion.
* A second LeanFinder search for ordered Cut maps and forests, and a grep of the project `WeilConjectures/`, found no duplicate declaration.  The complete raw search records are in `searches.jsonl`.

No statement correction, source error, `STATEMENT-DISPUTED`, new node, or dependency
module was needed.  The HA source is the online Higher Algebra Construction the project server
and Definition the project server/Remark the project server cited by the DAG node; the finite-forest
compatibility is the node's explicit expansion of those formulas.

## Second reading by Q70

I reread the DAG statement and the complete module after compilation.  Each chain,
forest, tree, interval, grafting, restriction, repeated-stage, successive-restriction,
and final compatibility clause has a corresponding declaration or `Compatible`
field listed above.  The theorem statement is verbatim in the node's `lean.statement`.
The only repair from the retained attempt was technical: explicit `autoImplicit false`,
`Fin` order proofs, removal of unsupported derived equality for the recursive `Tree`,
and parenthesization of the list-map expressions.  `scompile.py` now compiles the
module cleanly with no errors or warnings.
