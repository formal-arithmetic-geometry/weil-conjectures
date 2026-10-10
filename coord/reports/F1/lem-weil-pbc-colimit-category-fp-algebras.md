# lem-weil-pbc-colimit-category-fp-algebras

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-category-fp-algebras.json`: split Stacks Algebra 05N9(2)-(3) into three steps. No new nodes.

## Attachments

None. The item has no Lean declaration in either audited branch.

## Wanted

None. Stacks `algebra.tex` is available locally at `/tmp/stacks-project/algebra.tex`.

## Source and split

Read `algebra.tex` lines 32102-32216 and verified tags 05N8 = `lemma-algebra-map-property-in-colimit`, 05N9 = `lemma-colimit-category-fp-algebras` against `tags/tags`. The item states precisely 05N9(2)-(3), with both algebras finitely presented over the same stage. 05N9 refers to 05N8(3) for existence and 05N8(1) for eventual equality. Its proof assumes the base-changed target is the colimit of its stages; step 1 verifies this from the existing tensor-product pushout node and the categorical colimit node, including cofinality of indices above the fixed stage.

Step 2 takes the chosen finite presentation of the source, invokes the existing Mathlib leaf `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit` on the target colimit from step 1, and then the existing base-change universal-property leaf to produce the required stage map. Agreement after extension to the limit is checked on the source generators and coefficients. Step 3 takes finitely many algebra generators, applies the existing split node `lem-weil-pbc-directed-colimit-base-change-elementwise` to their image differences, moves the resulting zero equations to one common stage, and uses generation to equate the maps. With zero generators, the two maps already agree on the coefficient algebra.

The original item had no proof. Its statement and two statement dependencies are kept. No new node was required: DAG searches by tags `05N8` and `05N9`, by colimit/equality/base-change terms, and by the Mathlib candidate declarations found the seven cited public interfaces. The item already had LeanSearch, LeanFinder and source-grep searches for its non-leaf verdict. Existing node statements were read, not their proofs, for use: the colimit and finite-presentation definitions, tensor pushout, underlying ring colimit, finite-presentation factorization, algebra base-change adjunction, and elementwise base-change colimit.

Stacks 05N8's printed proof has apparent typos in its part (3) presentation (`N` is undefined and a generator is sent to a sum); the argument here uses the public finite-presentation factorization node, whose statement has the needed hypothesis and conclusion. The item statement is not changed.

## Verification

- `python3 tools/review_split.py lem-weil-pbc-colimit-category-fp-algebras`: PASS, 0 new nodes.
- `python3 tools/check_dag.py --cycles`: 0 cycles and 0 self-loops; seven unrelated existing reachability warnings.

## Unfinished

None for this one-level split. The cited base-change elementwise node has its own completed split.

## Review by F1

I read Stacks Algebra 05N9 (lemma-colimit-category-fp-algebras), clauses (2)-(3), and its cited 05N8 (lemma-algebra-map-property-in-colimit), clauses (3) and (1). The item has the same directed ring system, common stage and finite-presentation hypotheses. The printed 05N8 proof has typos in its presentation notation, but neither source statement nor the item's statement needs changing. There are no new nodes; the B1-B8 and duplicate-node checks are vacuous.

Step 1 uses the public tensor pushout and colimit universal properties to show that the base-changed target is the colimit over indices above lambda; the common-upper-bound calculation proves that upper set is cofinal. The public filtered-algebra colimit node supplies the corresponding underlying-ring colimit. Step 2 applies the public finite-presentation factorization leaf to that target and the public base-change adjunction to extend the stage map. Agreement at the limit is checked on algebra generators and coefficients. Step 3 applies the public elementwise base-change colimit statement to each difference of finitely many generator images, then uses directedness to choose a common stage. Those cited statements contain the precise facts used; the steps keep the descent argument in the item (C1-C4, D1-D5).

I checked an empty generator set, noninjective transition maps, and no least index in the original directed set. The proof only uses a chosen lambda and common upper bounds; it does not assume a transition map is injective. Equality after extension is handled as eventual zero of each image difference, not equality in the original stage (E1-E6). The worker needed no correction. review_split passes with no new node or route issue, and check_dag's seven reachability warnings are unrelated (A, F).

Before preflight I refreshed sheaf-dag and found blueprint metadata newly added to this node since the worker's base. I carried that metadata through byte-for-byte from the current base; the split does not change it.

The newer B9 check required completing that metadata. I searched the whole imported blueprint with `tools/blueprint_refs.py search 05N9`, `search finitely presented algebras colimit`, and a map-descent phrase. The nearby `lem-kun-fp-algebra-descent` concerns descent of a finitely presented algebra object, while this item concerns descent of homomorphisms and eventual equality, so `same_as` is empty. I checked the ancestor `lemma-weil-pbc-h1-constructible-representation` step 2; L had already completed its exact `from.place` on the current base, which I retained. I recorded in `split_report.blueprint` how this algebra tool serves that clause through the existing `via` chain. No new nodes were created.
