# Stage-1 report: lem-sfb-algebraic-stack-change-base-to-integers

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-stack-change-base-to-integers.json`: item, statement unchanged, eight proof steps, status split; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-stack-localization.json`: one new statement-only input, status unsplit; no Mathlib match. This is localization for ordinary étale stacks, without any algebraicity or geometric-property conclusion.
- `citations.json`: verbatim statement quotations for every dependency of every proof step.

There is one new node and zero Mathlib leaves. No unit, chapter, Lean, repository or launcher file was written. The scratch script and search log stay in the sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact item tag, algebraic-stack names and terminology, and change-of-base/localization terminology. No declaration of the project states the item. Searches for the new node's name, tag and stack-localization notion in both project source roots found no attachment either. Existing definitions under `Sheaf/` are vocabulary rather than proofs of this item.

## WANTED

None: the Stacks sources used here are present.

## Problems found and corrections

The item is mathematically sound under the usual meaning of 2-fibre product: a pullback of a diagram X -> Z <- Y. This does not mean that forgetting the base carries X times_S Y to the product over Spec Z. Step 5 states the actual comparison explicitly. For example, taking S to be two disjoint points and X=Y=S gives two points for the relative product and four for the absolute product; no such false product assertion is used. The item's final convention explicitly defines the absolute product separately, and I retained the statement verbatim.

The inherited source place attributed the phrase “think of X and Y as algebraic stacks over Spec(Z)” and proof of (5)-(8) to Tag 050M. In the local Stacks source this is Tag 050L, `lemma-separated-over-separated`. Tag 050M, `lemma-compose-after-separated`, has only four clauses. The analogous use in `lemma-separated-implies-morphism-separated` is Tag 050N. I corrected only the source locator. The mathematical proof uses 04X5/04WV, the existing space theorem, and the qcqs definitions, not an uncited separation theorem.

The inherited blueprint anchor was null: `blueprint_refs.py ancestor` likewise returned None because the creation chain eventually terminates at a Lean module name. The inherited place explicitly names `det-thm-sf-ctf-stability-direct-images`, and that node is an imported blueprint node. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`: paragraph (3) is the open/direct-image preservation argument. The dry run requires the new node's `from.node` to equal the ancestor helper's actual output, None. I therefore retained the null ancestor on both files, named the current blueprint proof and paragraph explicitly in `from.place`, and retained the inherited intermediate chain and unit. The missing formal ancestor is documented rather than inventing a different creation history. No unit or chapter route is changed.

During my self-review I made the converse diagonal's change of algebraic-space base explicit and added its space-theorem citation to step 4. This avoids treating an absolute algebraic space with a map to S as a relative space without the needed theorem.

## Searches and reuse

The whole-DAG tag searches included 04X5, 04X6, 04WV and 04WT, and searches for smaller-base schemes, change of base scheme, localization of fibred groupoids and stacks over slice sites. `blueprint_refs.py search` was run for “change base scheme”, “localize stacks”, “localized site”, “stack localization”, “etale stack”, “algebraic stack” and “04WV”; all returned zero blueprint matches. I opened the closest existing stack equivalence statements rather than relying on their titles. I reused `lem-sfb-space-change-base-to-integers`, which supplies the space equivalence, chart comparison and fibre-product comparison.

All Mathlib searches were run through the required `msearch.py` command and are recorded from `searches.jsonl`. For the item the hits are scheme smoothness, scheme étale categories and `AlgebraicGeometry.specZIsTerminal` (`AlgebraicGeometry/Limits.lean:50`), which does not address stacks. Two different natural-language formulations were tried for localization. I also read `CategoryTheory/Sites/Descent/IsStack.lean:49`, `DescentData.lean:511` and `:603`, `Precoverage.lean:412`, and `CategoryTheory/Comma/Presheaf/Basic.lean:613`. The IsStack results say that a single pseudofunctor satisfies effective descent; `isEquivalence_toDescentData` concerns a covering family's descent category. `overEquivPresheafCostructuredArrow` is an equivalence for set-valued presheaves. None is the asserted equivalence of 2-categories of groupoid-valued étale stacks. The initial unqualified Loogle names were unknown; the subsequent fully qualified `CategoryTheory.Pseudofunctor.IsStack` query succeeded and its hits were inspected. No unavailable service was counted as evidence of absence.

## Not duplicates

- `lem-sfb-etale-stack-localization` vs `lem-sfb-space-change-base-to-integers`: the new node concerns arbitrary étale stacks, including non-discrete fibres and no algebraic diagonal or atlas hypothesis; the existing node concerns set-valued algebraic spaces and their charts/ringed sites. Neither gives the other by specialization to the same object class.
- `lem-sfb-etale-stack-localization` vs `lem-sfb-stack-fully-faithful-local-equivalence`: the latter tests one given functor between stacks on the same site for equivalence; it does not construct a stack on a different base site or give the equivalence of 2-categories of pairs.
- `lem-sfb-etale-stack-localization` vs `lem-sfb-fibred-groupoid-equivalence-criterion`: the latter assumes a cartesian functor over a fixed category and fibrewise equivalences; it gives no change-of-site descent assertion.
- `lem-sfb-etale-stack-localization` vs the item: it has no algebraic-space diagonal, smooth atlas, algebraicity, qc or qs conclusion. Those are checked in the item's own steps, rather than moved into the new node.

No existing node was found with the new node's Stacks tag 04WV. The new input is the non-elementary stack-localization result explicitly invoked by the source proof of 04X5. The elementary calculations with triples, diagonals and atlas witnesses remain proof steps, not extra nodes.

## Review by Q62

I read algebraic.tex 04X5 (`lemma-category-of-spaces-over-smaller-base-scheme`) and 04X6 (`definition-viewed-as`) in full, including the source's appeal to stacks.tex 04WV. I read Constructions A and B in stacks.tex 04WT and the whole statement of 04WV. The new node is its scheme-site specialization for étale coverings, matching the project's actual stack convention in `def-sfb-stable-pointed-moduli-groupoids`. The site theorem is not limited to the fppf topology. The representable stack h_S is the category Sch/S over Sch/S'; there is no choice of atlas in that new statement. The node has no proof, no proof dependencies and no proof sketch embedded in its statement.

I also read spaces.tex 03I4 (`lemma-change-base-scheme`) and 04SG (`lemma-category-of-spaces-over-smaller-base-scheme`), and opened the complete statement of `lem-sfb-space-change-base-to-integers`. Its first clause gives algebraic spaces and identical étale scheme charts, its second clause gives the inverse correspondence for spaces equipped with a map to S, and its fibre-product clause is the pullback comparison actually needed. I read `def-sfb-algebraic-moduli-stack`, `def-sfb-stable-pointed-moduli-groupoids`, `def-sfb-stack-qcqs-morphism` and `def-pc-fibre-product` in full. The following are statement-level uses, not uses of constructions hidden in a dependency's proof.

1. Step 1 uses only the new ordinary-stack localization equivalence. Its statement includes both directions and the action on 1- and 2-morphisms. The hypotheses are schemes in a common allowed universe; there is no finiteness or separation premise.
2. Step 2 uses the scheme fibre-product universal property to construct E, the fibred-groupoid/discrete-scheme convention to force equality of the two S-maps, the algebraic-stack definition for the relative diagonal's Isom space, and the space theorem applied to E -> T. These say exactly what the step takes from them. The equality test is written out; E is not assumed to be an immersion of a particular kind or quasi-compact.
3. Step 3 uses the explicit triple definition of 2-fibre products, the space theorem's chart/base correspondence, and the atlas definition's smoothness/surjectivity tests on scheme charts. Each projection to T is the same scheme morphism, so no unstated theorem on smoothness after changing the structural base is needed. In the reverse direction U receives its S-map by composition through the given q.
4. Step 4 uses the same fibred-groupoid convention and space equivalence to identify the reverse diagonal, then the algebraic-stack definition and the new stack equivalence to restrict to algebraic stacks. I corrected this step to cite explicitly the inverse space correspondence. It does not infer algebraicity merely from ordinary-stack descent.
5. Step 5 uses the cited triple-and-arrow formula for the fibre product; the existence of alpha forces equality of the maps to S because the maps f and g are over S. Both objects and arrows, and both projections, are identified. This is an elementary calculation from that definition, not a claim about absolute binary products.
6. Step 6 applies the qc definition to the identical atlas witnesses from step 3. Then every absolute test stack over the target receives an S-map, is algebraic by step 4 and has the same pullback by step 5. Thus the universal quantifiers in the qc-morphism definition match. No qc hypothesis on S or on the chosen target is introduced. This is a short assembly from previous steps and the cited definition.
7. Step 7 uses the space theorem's atlas and inverse equivalence and its fibre-product clause. The cited qcqs definition gives exactly qc space charts, qc test spaces and qs as qc of the relative diagonal. Applying the qc comparison to the very same relative diagonal proves the space qs comparison; no stack-to-space qc equivalence is assumed.
8. Step 8 uses the stack qs definition's scheme tests of the relative diagonal, the earlier triple comparison and step 7's space properties. The cited space equivalence supplies the base correspondence for each represented fibre. This checks representability as well as qc and qs, in both directions, rather than dropping a clause of the project's predicate.

For the qcqs conventions I checked stacks-properties.tex 04YC(3), stacks-morphisms.tex 050U (`definition-quasi-compact`) and 04YW(4) (`definition-separated`), in addition to the node's full statement. The atlas convention is used as the definition, so the topological equivalence theorem 04YC is not silently used as an additional lemma.

Small cases checked: the empty base/empty stack, the identity base change, a non-quasi-compact base with a quasi-compact atlas source, non-separated S (the equalizer construction in step 2 still works), the two-point product example above, and stacks with nontrivial stabilizers (all isomorphisms remain, so nothing assumes Deligne--Mumford or representable f). No new statement excludes a characteristic or requires S separated. Every proof step is under 2000 characters. The ordinary localization result is the sole new non-elementary input; no clause of the item's geometric conclusion was made into a new node. The proof's direct Isom verification is an agent-written expansion/adaptation of 04X5, honestly marked `proof_origin.by=agent`. B1-B9, C1-C8, D1-D5 and E1-E7 were checked against the files and source passages above; no SGA source is used.

## Unfinished work

The new ordinary-stack localization node is intentionally unsplit, as required for a one-level stage-1 delivery. No part of the item's proof is left as a reference in place of an argument. The required server checks and delivery are run after this report is written.

## Validation

The standalone server `review_split` passed. The first full dry run reported only B9: the new node used the explicitly named blueprint proof as `from.node`, whereas the ancestor helper returns None. I repaired both files to retain that actual null ancestor and documented the exact proof place instead. A subsequent full dry run is required before the push.
