# Stage-1 delivery: lem-sfb-profinite-action-finite-quotients

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-finite-quotients.json`: statement item, now split into ten proof steps. No exact Mathlib match for the full equivariant statement. The statement, source, created record and inherited blueprint provenance are preserved.
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl`: actual search-command records, retained and incorporated in the item's searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Three existing Mathlib leaves are reused: `lem-weil-pbc-profinite-clopen-basis`, `lem-weil-pbc-compact-hausdorff-bijection`, and `lem-weil-pbc-tychonoff-product-quasi-compact`. The existing size convention is the sole statement dependency.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, profinite actions, invariant partitions and related terminology. There is no declaration with this blueprint tag. The candidate `AlgebraicGeometry.exists_finite_invariant_clopen_partition` in `WeilConjectures/AlgebraicGeometry/GaloisFiniteInvariantClopenPartition.lean:140` concerns a Galois field extension, a scheme base change, and a single nontrivial partition invariant under automorphisms over a finite intermediate field. Its hypotheses and conclusion are different, and it does not establish this general compact-space action statement. It is not an attachment.

## WANTED

None. All sources used were present locally.

## Errors and corrections

No statement dispute or correction. The unsplit item had no proof. I supplied the compact-action argument omitted by the identification in Bhatt–Scholze Example 4.1.10, then followed the clopen-partition reconstruction in Stacks Tag 08ZY. The proof is explicitly agent-written; the source's identification is not being presented as if it supplied the missing argument verbatim.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor lem-sfb-profinite-action-finite-quotients` confirms that there is no imported blueprint ancestor in the creation chain. I retained its non-unspecified `from.place` and `via`, and explained the source paragraph in `split_report.blueprint`. Searches over the whole imported blueprint for profinite, invariant clopen, continuous G, finite discrete, and compact product terminology produced no equal statement. The supplied unit is inherited from the larger constructible finite-Tor route; this is a generic topological sublemma, not that unit's key statement. No unit or chapter record was changed.

## Mathlib search assessment

The complete statement was searched with leanfinder, leansearch, loogle and grep using the required search command, with a second semantic phrasing focused on clopen stabilizers. All services answered successfully. The recorded results are the actual log records. `Profinite.asLimit` concerns ordinary discrete quotients without a group action; `ProfiniteGrp` limits concern groups, not arbitrary acted-on spaces; `ContAction` defines a category, not the finite quotient theorem; and the Galois-category finite-action results do not construct invariant clopen quotients of a given profinite action.

The auxiliary tube-lemma search found `generalized_tube_lemma`. I did not add a node: step 1 gives the needed finite-subcover argument directly from continuity and the definition of compactness. Likewise I did not add an open-subgroup finite-index node: step 2 takes a finite subcover of the open coset cover. The arbitrary compact-product searches found `Pi.compactSpace`, whose pinned source I read at `Mathlib/Topology/Compactness/Compact.lean:1183`. A whole-DAG search found the existing Tychonoff leaf, so the proof cites that leaf. No auxiliary result has been misreported as a match for the complete item.

## Not duplicates

No new nodes are proposed. Existing ordinary clopen-partition realization and profinite-span approximation nodes were inspected; they do not assert the equivariant refinement theorem. The clopen-basis, homeomorphism and Tychonoff statements are cited as existing nodes.

## Review by NN

I read Bhatt–Scholze, *The pro-étale topology for schemes*, Example 4.1.10 on printed/PDF page 28. Its identification of pro-finite-discrete-G-sets with profinite continuous G-sets is the mathematical purpose of the item. I also read Stacks `topology.tex` Tag 08ZY (`lemma-profinite`, including both directions and the partition construction), Tag 005D (`lemma-intersection-closed-in-quasi-compact`), Tag 08ZU (`theorem-tychonov`), Tag 08ZV (`lemma-inverse-limit-quasi-compact`), Tag 0A2P (`lemma-describe-limits`, especially its product/subspace construction), and Tag 08YE (`lemma-bijective-map`). There are no new-node sources to check. I read the supplied chapter and unit records and the three-level route rules; the proof develops only the generic topology input on the existing field-site route.

Step 1 uses no external theorem: continuity supplies open rectangles, compactness of P supplies finitely many of them, and the assumed open-normal neighbourhood basis supplies N. For y in a chosen W_x, both points lie in the same original block, so the rectangle really gives preservation of that block. Inverses inside N turn inclusion into equality. This avoids the invalid inference that pointwise open stabilizers automatically give a uniform subgroup without using compactness.

Step 2 also uses only definitions and finite constructions: open cosets cover compact G, so finitely many representatives suffice. N preserves each original block, so gN has a single effect on that partition. The common refinement of the entire finite orbit, rather than just an arbitrary finite selection of translates, is permuted by G. Continuity of translations and their inverses proves that all its blocks are clopen. No new node restates either of these substantive clauses of the item.

Step 3 cites `def-weil-size-convention`, whose statement fixes the universes and small representatives. Partitions are subsets of the power set of the power set of the small P, so the index set stays small. Intersections prove directedness, and the containing-block maps are uniquely determined and compose. A point in a coarse nonempty block supplies a finer block, which verifies surjectivity rather than assuming it.

Step 4 uses no cited theorem. The action on parts and the quotient equivariance are formulas. Its continuity proof uses a chosen point in each nonempty block and the equality gB=C iff gx_B belongs to C; this equivalence depends on invariance and disjointness, both available. It proves joint continuity on G times the finite discrete block set, not merely continuity for each fixed group element.

Step 5 cites the exact statement of `lem-weil-pbc-profinite-clopen-basis`. I opened that node: it supplies a clopen neighbourhood inside any open neighbourhood, for compact Hausdorff totally disconnected spaces, precisely the hypotheses of P. Its point-separating clopen partition can be refined by steps 1–2. It is not being asked to supply invariant refinement. This proves injectivity.

Step 6 is the finite-intersection proof written out, with no external theorem hidden under the tag. Directedness and compatibility give a nonempty finer block in any finite intersection. Empty total intersection would give an open cover by complements and hence a forbidden finite subcover. Thus compactness, not a presupposed inverse-limit surjectivity theorem, realizes the coherent family.

Step 7 cites `lem-weil-pbc-compact-hausdorff-bijection`. I opened it and verified that its conclusion is a homeomorphism for a continuous bijection from a quasi-compact subspace to a Hausdorff subspace. Applying it to the whole P and whole L is valid. Continuity is checked on finite cylinders, Hausdorffness is established by separating distinct coordinates, and bijectivity is already proved. Equivariance is the coordinate formula; compatibility is preserved by equivariance of the transition maps.

Step 8 cites `lem-weil-pbc-tychonoff-product-quasi-compact`. I opened its full statement: it applies to a set-indexed product of arbitrary quasi-compact spaces with exactly the product topology used here. Every finite discrete Q_i is compact by its finite underlying set. The compatibility locus is closed by an explicit open-cylinder neighbourhood of every failed equation. The open-cover proof with the complement shows the closed subspace is compact. I did not take a group-valued inverse-limit theorem as if it stated the result for sets.

Step 9 proves Hausdorffness and total disconnectedness directly by coordinates. For any subset with two distinct points, a distinguishing coordinate cylinder is a nontrivial clopen subset in its relative topology, hence a separation. No unsupported claim about preservation of connectedness is needed.

Step 10 uses the assumed equivariance and continuous joint actions at every finite stage. The compatibility equations survive the action by a displayed calculation. The inverse image of a finite basic cylinder is a finite intersection of opens under maps G times Q to Q_i, each of which is the composite of the projection with the given joint action. Thus it proves the required joint continuity, including for the partition system.

I checked every cited statement against its use, and wrote the exact supporting sentences in `citations.json` (including the whole product-compactness conclusion). I checked sections B–E of `coord/delivery-errors.md`: the statement is self-contained, its only named notion has its existing definition dependency, there are no new unsplit nodes or duplicated clauses, every external non-elementary fact is cited, and the other steps give their elementary arguments rather than merely naming a tag. All ten steps are below 2000 characters; none hides an unproved comparison or unnamed standard lemma.

Edge cases checked: P empty gives one empty partition and an empty limit; a singleton or trivial group gives the expected trivial finite quotients; a transitive finite action refines to the singleton partition, even when the starting partition is not invariant; a coarse nonempty block always has a finer block for surjectivity; an empty Q_i forces the whole product and limit empty; non-surjective transition maps remain allowed (for example all transitions of a constant two-element tower projecting to a fixed point). The converse never uses surjectivity, nonempty stages, or nonempty limit. No hypothesis of freeness, faithfulness, metrizability, countability or a uniform finite quotient acting on all of P is introduced.

## Unfinished work and validation

No mathematical part is left unfinished. No Lean was written or compiler/build command run, and no repository or launcher file was modified. The required server dry run and final delivery are the remaining validation and publication steps; their actual command outputs determine delivery success.
