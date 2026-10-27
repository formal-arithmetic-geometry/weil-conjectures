## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fixed-arrow-scalar-extension-diagram.json`: statement, split into eight proof steps; no exact Mathlib match for the full conjunction. All statement and maintainer fields retained.
- `citations.json`: a verbatim statement quotation for every node cited in every proof step.
- `searches.jsonl`: actual search-command results, retained without alteration.

No new nodes; zero new Mathlib leaves.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag and fixed-arrow/scalar-extension concepts. `AlgebraicGeometry/ScalarExtensionChainHomDiagram.lean:246` concerns derived Hom diagrams of complexes and explicitly asserts no colimit property of its cocone, so it does not state this item. Mathlib `TensorProduct.directLimitRight` (`LinearAlgebra/TensorProduct/DirectLimit.lean:97`, generator formula at 103) treats a fixed base ring. `LinearMap.baseChange_comp` and `baseChange_baseChange` (`LinearAlgebra/TensorProduct/Tower.lean:690,695`) handle individual maps and comparisons. They do not attach the full changing-ring arrow theorem.

## WANTED

None. All sources needed for this split were available locally.

## What was wrong or missing

The item was a statement-only node, without proof or Lean audit; its statement is correct. No STATEMENT-DISPUTED and no statement correction. The construction source Tag 00QX ends with details left to the reader. Those details, for the fixed-stage rather than newly descended presentation, are written in the proof. Tag 046Y's first paragraph motivates treating the two modules and their arrow simultaneously, but it is not cited as a replacement for those calculations.

The existing presentation-diagram nodes need finite-type integer algebras and/or construct an unspecified final refinement. They cannot be used directly for the supplied arbitrary ring diagram and its specified maps. The existing `lem-weil-pbc-base-change-diagram-elementwise` does apply after the tensor comparisons have been proved. Its statement gives representatives and eventual zero, not the abelian-group colimit universal property; Step 8 proves the latter explicitly. This distinction avoids using the proof of a cited node as if it were its statement.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their own statuses. No Lean was written or compiled, no agents were started, and the shared repository and launcher scripts were read only.

## Not duplicates

No new nodes were created. Searched the whole DAG for Tags 00QX and 046Y, tensor-colimit, tensor finite products, base-change diagrams, finite presentations, and elementwise colimits; read the relevant existing statements and reused them. Blueprint searches for `scalar extension`, `scalar-extension diagrams`, `base-change diagram`, `tensor.*colimit`, `tensor products commute`, and `finitely presented module` produced no alternate blueprint statement of this full item. `blueprint.same_as` remains empty. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality`; its current main-20261015 text was read, including the normal-cone route. No chapter or unit record was changed.

## Review by Q19

I read Stacks `algebra.tex`, Tag 00QX (`lemma-limit-module-essentially-finite-presentation`), its six clauses and its finite presentation-matrix proof, and Tag 046Y (`lemma-mod-injective-general`), especially the simultaneous-arrow construction in the first paragraph. I also read the tensor universal property and its balanced construction (00CX), the flip/direct-sum/unit formulas (00CY), tensor-colimit compatibility (00DD), right exactness (00DF), and the common-stage descriptions (00D6, 00D7). For the directed tail I read `categories.tex`, `lemma-cofinal-in-filtered` (0BUC) and `lemma-cofinal` (04E7), checking the tags against `tags/tags`. The proof is marked agent-written because it supplies the omitted fixed-stage details, using these source constructions. There are no new nodes needing sources or separate small-case tests.

I opened every cited node and checked the following against its statement, rather than relying on its title or proof:

1. `lem-weil-pbc-colimit-initial-full-subcategory` clause (1) is phrased for a cofiltered category and an incoming full subcategory. Applying it to the opposite of I gives exactly cofinal upper-tail restriction for the ring diagram. Smallness passes to the full subpreorder; c is a member, and any upper bound of two tail indices remains above c. Existence of the restricted ring colimit follows from the existing cocone being a colimit, not an extra hypothesis.
2. `def-weil-pbc-module-tensor-product` includes the balanced construction, universal property, and pure-tensor generation. I checked R-linearity of all ring transitions via the diagram identity and cocone compatibility. The displayed calculation proves semilinearity for the varying stage rings. Identity, composition and cocone laws are verified on generators, not assumed from a definition of a diagram.
3. The same tensor node defines the induced map for an R-linear v. The two sides of each arrow square send x tensor a to the identical displayed tensor, so both stage and limit arrow compatibilities really follow.
4. `def-sc-finitely-presented-module` supplies finite free presentations, and `lem-weil-pbc-tensor-right-exact` preserves their final exactness without flatness. `lem-weil-pbc-tensor-finite-product` includes t=0 and identifies the finite free terms after scalar extension. The tensor unit map and its inverse are written explicitly. Exactness over R is also exactness for these B-linear maps on underlying groups, hence is a finite B-presentation. I did not use the similarly titled finite-presentation base-change/composition node, which is about algebras rather than this module assertion.
5. The tensor node supplies the two balanced maps F and G; the proof writes the R-balancing check of G and the two inverse identities. The same calculation applies with B=A_k and B=A and with T=P and T=Q. This proves every specified comparison, not just existence of an unspecified isomorphism. It uses no flatness or cancellation. This is a direct few-line inverse-map verification, not a hidden separate tensor-associativity theorem.
6. Both orders of the arrow comparison send an iterated generator to v(x) tensor h(a)b. Thus the comparison maps from Step 5 intertwine the actual extensions of v_j; no unspecified naturality claim is used.
7. `lem-weil-pbc-base-change-diagram-elementwise` assumes precisely a nonempty directed ring colimit, semilinear additive diagram/cocone, and canonical transition and limit tensor isomorphisms. Steps 1,2,5 supply every assumption. Its tensor factors are written in the reverse order, so the proof writes the balanced flip and identifies the canonical maps on generators. The node promises representatives and eventual zero, which are exactly what is taken from it. Equality of two arbitrary stage representatives is proved by taking their difference at a common index and applying eventual zero. None of its dependency paths reaches this item (checked by traversing statement and proof dependencies), so this reuse does not create a cycle.
8. The colimit definition `def-weil-pbc-category-colimit` gives the universal property. Step 7 supplies every representative and detects equality. The map to any compatible additive cocone is therefore well defined, additive by a common-stage sum, and unique by surjectivity of the representatives. No target module structure on the arbitrary abelian group H is assumed. This establishes the colimit in the exact coefficient category claimed by the item.

I checked B--E of `coord/delivery-errors.md` against the files. There are no new definition-only citations hiding a non-elementary theorem: the non-elementary inputs are the cofinality, right-exactness, finite-product and elementwise nodes. The other steps are explicit balancing, inverse, generator and universal-property arguments. Each step is below 1000 characters, so none conceals a lemma in a step over 2000 characters. Every `uses` entry has a quotation in `citations.json`, and `proof_deps` is exactly their union. Off-unit algebraic tools are declared in `split_report.tool_uses`; the normal-cone unit route is unchanged.

For edge cases, I checked a singleton tail (all comparison maps reduce to the tensor unit isomorphisms), zero modules and the zero arrow, empty presentations, zero rings, and a nonflat quotient transition such as Z to Z/2. The inverse comparison remains valid even when the transition module map is not injective: eventual-zero detection is allowed and does not assert injective transitions. Directedness is used only to reach common stages. No Noetherian, nonzero or flatness condition was introduced. All constructions take place in a common large universe, as allowed by the item.

The item’s inherited Mathlib searches were retained. Six additional searches were actually run by the prescribed `msearch.py` command and their log/results were read: Loogle, LeanSearch, two LeanFinder phrasings and two grep searches. I read the fixed-base tensor/direct-limit equivalence and base-change composition source and the module filtered-colimit source. These are useful component tools, but not a one-line match for the entire item. The first grep includes algebra rather than module finite-presentation hits, which are not treated as module matches.
