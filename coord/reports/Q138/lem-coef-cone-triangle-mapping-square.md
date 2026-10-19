# Q138: lem-coef-cone-triangle-mapping-square

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cone-triangle-mapping-square.json`: statement, split; five explicit elementary steps from the coherent-realization definitions. Mathlib verdict: no match. No new nodes and no Mathlib leaves.
- `citations.json`: six step/node records, with exact statement quotations.
- `report.md`: this delivery report. `searches.jsonl` is the search command's own log; `prepare_split.py` is sandbox-only preparation code.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for coning/coherent-cone/homotopy-coherent/rigidification terms, and checked the upstream-name index. No project declaration states the item. The rigidification hits concern line bundles rather than coherent realization. Upstream master is reference material only and supplies no attachment.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, Section 1.1.5, Notation 3.2.1.1, Definition 3.2.1.2 and Proposition 3.2.1.11(4), for lem-coef-cone-triangle-mapping-square. HTT is not archived in `literature/`; the cited IAS PDF was read online. No file was downloaded into the repository. The detailed cube calculation is an agent-written proof and is marked accordingly. Its blueprint-origin document is the current ancestor proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`.

## Audit of the input

The statement is correct and unchanged; there is no STATEMENT-DISPUTED. The item initially had an empty proof. I supplied the degreewise square rather than restating its existence as a new lemma. In particular, its top boundary is computed as a union of subset chains; it is a marking generator because the coning edge of the degenerate input edge at z is itself degenerate. The proof never assumes that markings are closed under composition.

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, the current ancestor statement/proof, the historical ancestor, and the parent `lem-coef-marked-cone-generator-calculations` (especially steps 9 and 11). This is foundation work below that parent's generator calculation, not a replacement of the unit's route. The item's inherited blueprint provenance already specifies that foundation chain and remains intact. The item is not the key node of its unit, so no realized fields need changing. No source, target, unit, chapter, or maintainer-owned field was changed.

## Unfinished work

None within this item's stage-1 scope. Its existing dependency nodes remain separate DAG tasks. No Lean was written, compiled, or built.

## Not duplicates

There are no new nodes and therefore no new/existing tag pairs. Whole-blueprint searches for `cone triangle mapping square`, `coning triangle`, `triangle squares`, and `marked cone` returned no same-statement blueprint node; `same_as` remains empty. A broader `subset` search was also inspected. Searches over `dag/nodes` found the parent generator calculation, coherent-realization nodes, cone-boundary cells, ordered-simplex evaluation, and join-boundary cubical extension. None supplies this marked triangle-square statement without doing the displayed calculation; several instead lie above it in the dependency graph. I reuse the existing coherent-realization and marked-object nodes and create no replacement fact.

## Mathlib searches

The item's inherited Q103 searches are retained verbatim. Q138 additionally ran the logged msearch leanfinder queries in two phrasings, loogle, grep, and leansearch, with exact queries/results appended to `mathlib_searches`. No unavailable service is reported as an empty result. The HornColimits hits state pushout squares of subcomplexes; the LeanSearch mapping-cone hits concern cochain complexes; the grep hits concern ordinary categorical cones. The second LeanFinder query found `SimplicialThickening.comp_I`, `compFunctor` and the enriched composition definition in `Mathlib/AlgebraicTopology/SimplicialNerve.lean`. I read lines 80–148: these give union composition/direct images for ordered simplices but not the general simplicial-set cone, its triangle square or its marking clauses. I also read the product-simplex coordinate description. Those definitions help explain why the proof is elementary; they are not a declaration stating the whole item or a one-line specialization of it.

## Review by Q138

I checked the item against HTT's online Notation 3.2.1.1 and Definition 3.2.1.2 (printed pp.170–171) and the square in Proposition 3.2.1.11(4) (printed p.175). That displayed square is a special inverse-triangle instance. The arbitrary-triangle version here is proved directly from the subset-poset definition, not inferred from the proposition's Kan hypothesis. There are no new nodes needing additional sources. No SGA text is used.

For C4 I opened and read the complete statements of both cited nodes. `lem-coef-coherent-nerve-comparison` expressly defines the subset-poset mapping sets, union composition, simplicial categories and coherent-realization functor; I use only those definitions, not its Quillen-equivalence conclusions or its proof. `lem-coef-marked-point-cartesian-model` expressly defines a marking as containing all degenerate edges and maps as preserving markings; no fibrancy or localization assertion from it is used. Every step/node occurrence has a verbatim quotation in `citations.json`.

Step 1 uses the coherent-realization definition to send a pair of monotone binary sequences to its explicit subset chain. I verified inclusions and compatibility with every simplex operator, so this defines a whole simplicial square. Applying the coherent functor of the coned input simplex requires only a map, not an embedded simplex.

Step 2 uses union composition from that same statement. I recomputed all four vertices and all four chains: the bottom and left chains lie in the two coning faces, the right chain is union with the constant edge 01, and the top chain is union of the coherence chain 02 ⊆ 012 with the cone edge 23. This verifies equalities of boundary edges, including their directions, rather than just endpoint coincidences. The diagonal and the two triangles are already present as simplices of the product.

Step 3 uses the coherent-realization operators and the marked-object definition. For the collapse [2] → [1] taking 0,1 to 0 and 2 to 1, both endpoint subsets of the coning chain have the same image. Thus its edge is degenerate. With d = s₀z and g = ρσ, the diagonal action is literally the stipulated generator. When k is degenerate the same calculation makes its coning edge degenerate. This is the only marking argument; no saturation, Kan property, or equivalence criterion is hidden in it.

Step 4 uses the associative unital simplicial composition expressly stated in the coherent-realization node. An acting vertex becomes a constant acting edge, and composition with g stays an edge of the required mapping simplicial set. I checked the source and target objects of g ∘ s₀a. Simpliciality handles the degenerate marking generators, and restriction of a composite square gives exactly the precomposed four edges.

Step 5 checks the hypotheses used in the previous steps: no horn fillers, injectivity, local Kan condition, or finiteness of K was used. I tested K empty (vacuous), K a point (the constant triangle gives a constant square), and degenerate triangles s₀e and s₁e. Under either degeneracy, direct images identify the appropriate subset vertices and boundary chains, and all formulas still hold. The case of a nondegenerate 2-simplex with repeated vertices also works because its induced functor, rather than a vertexwise embedding, is used throughout.

For C1 and D1–D5, the five steps are explicit applications of the cited definitions: no standard lemma or non-elementary comparison is suppressed, and no new node merely relocates an item clause. The two-element chain computations, constant-subset image calculation and associativity identity are elementary. Step lengths are 822, 956, 918, 743 and 627 characters, all below the 2000-character review threshold. I checked every clause is covered, statement dependencies remain the original two notions, proof_deps is exactly the union of uses, no ancestor is cited as a dependency, and no off-unit tool is needed.
