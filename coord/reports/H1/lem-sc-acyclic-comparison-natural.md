1. Files written

- `dag/nodes/sec-picard-framework/lem-sc-acyclic-comparison-natural.json`: statement, four-step proof, proof dependencies, split report; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.

2. Attachments

None.

3. WANTED

WANTED: `literature/stacks-project/derived.tex`, Tag 015E, for the naturality paragraph of the acyclic-resolution comparison. The local literature checkout contains the citation index but not the TeX source; the proof is recorded as agent-written from the stated Tag 015E argument.

4. Problems found

The imported item had no proof and was marked `unsplit`. Its statement is mathematically the naturality assertion used by the neighboring derived-composite node. The imported dependency `lemma-weil-pbc-leray-acyclicity` supplies the comparison maps but not the naturality proof, so the split explicitly supplies the lift square, homotopy uniqueness, additive homotopy invariance, and the derived-functor map formula. No statement was changed and no duplicate child node was needed: all four facts already exist in the DAG.

5. What remains

Nothing remains for this split. The source TeX itself was unavailable locally, as recorded under WANTED.

## Review by H1

I read the item node and its consumer `lem-sc-ext-derived-composite-natural`, and checked the item statement against the Stacks Tag 015E description recorded in the node. The item introduces abelian categories, enough injectives, a left exact additive functor, acyclic resolutions, a morphism of resolutions, and the comparison maps; its hypotheses are used unchanged in the proof.

Step 1 cites `lem-weil-pbc-injective-resolution-lift-exists` for the existence of all three resolution lifts and cites the exact sentence in `lemma-weil-pbc-leray-acyclicity` saying that the comparison map is induced by any lift into an injective resolution. `def-sp-injective-resolutions` supplies the resolution meaning. Step 2 uses the exactness in the acyclic-resolution definition to observe that the augmentation is a quasi-isomorphism and monomorphism, then applies the cited lift-uniqueness node, whose statement has precisely the quasi-isomorphism and injective bounded-below target hypotheses. Step 3 uses the additive clause of `def-sp-left-exact-additive` and the cited homotopy-invariance node; that node explicitly states both termwise preservation of homotopies and equality on cohomology. Step 4 uses the cited derived-functor-map node, which states exactly that the cohomology map of a lifted morphism is `R^n v(h)`, yielding the displayed equality after rewriting by `c_I^n` and `c_{I'}^n`.

I searched the whole DAG and the Lean source for the item tag, its key phrases, and possible comparison-lift declarations. No Lean declaration states this item. The existing nodes used above were opened and their statements match the uses recorded in `citations.json`; no new node was created. I checked the edge cases `n=0`, `h=id`, and the zero functor: the square reduces respectively to the degree-zero identification, identity naturality, and equality of zero maps. The only unresolved environmental issue is the unavailable local copy of `derived.tex`, reported as WANTED.
