# Worker report: lem-sfb-descent-data-refinement-hom

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-descent-data-refinement-hom.json`: item, statement, split in five steps. Statement unchanged. Mathlib verdict: related machinery, no exact match or one-line specialization.
- `citations.json`: one verbatim statement quotation for each of the three citations in step 1.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The geometric permanence input is an existing Mathlib leaf. The remaining operations are the item's assumed Hom bijection, explicit conjugation by descent isomorphisms, and cocycle equations, so creating nodes for them would introduce elementary nodes or restate the item.

## Attachments

None. The project search found no declaration tagged with this item. I read `WeilConjectures/Mathlib/CategoryTheory/Sites/Descent/Precoverage.lean`, especially lines 31-42 and 292-307: `CategoryTheory.Pseudofunctor.DescentData.bijective_pullFunctor_map_of_isSheaf` requires a Grothendieck topology, covering membership, and sheaf conditions on Hom presheaves. Supplying those from the present single-map hypothesis needs an argument. The fpqc refinement files treat schemes over schemes and fpqc covers, rather than an arbitrary category-valued pseudofunctor, so neither is an attachment.

## Literature wanted

WANTED: David Rydh, *Submersions and effective descent of étale morphisms*, version 2010-03-03, Proposition (5.6), printed p.19, for lem-sfb-descent-data-refinement-hom. There is no local PDF in literature. I read [the online PDF](https://davidrydh.se/papers/submersion20100305.pdf), including Notation (5.1), Remark (5.2), and the definitions and reduction propositions on printed p.19. Proposition (5.6) records composition and refinement for universal effective descent in a category fibred over schemes; it does not separately state or prove this Hom-only supporting assertion. The proof is therefore explicitly marked agent-written. Its content is supplied in the item, without using a cited source's omitted proof or any SGA source.

## What needed repair

The imported item had a complete inline definition of the pseudofunctor, descent data, and universal descent, but no proof. Its statement is correct and remains byte-identical. I filled the missing Hom argument. In particular, one cannot descend directly along a: it has no descent hypothesis. Instead the arrow is first constructed on W=U times_S Y and descended along q:W to Y, a base change of p=ba. The graph U to W only verifies the restriction, without any covering claim about that graph.

The supplied blueprint ancestor is null. `tools/blueprint_refs.py ancestor` confirms this. I retained the full supplied via chain and from.place, and documented in split_report the support of current latest `sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), through the established alteration/moduli support route. I also read the chapter and unit records and current latest direct-image proof. No chapter, unit, or unit route is changed.

## Searches and Not duplicates

No new nodes were created. I searched the whole DAG for universal descent and refinement full faithfulness, and the whole imported blueprint with `blueprint_refs.py search` for `descent data`, `refinement`, and `universal descent`. None states this general Hom-only lemma. The existing fpqc refinement lemma assumes both covers fpqc and concerns the fibre category of schemes. The cartesian-section restriction lemma assumes a site, a prestack in groupoids and a locally covering inclusion of sieves; its objects, hypotheses and conclusion differ from this arbitrary fibre-category/single-map statement.

The inherited search results remain in the item. I read them and the candidate hypotheses, then ran five logged searches for this item through msearch.py: two different LeanFinder phrasings, Loogle for fullyFaithfulPullFunctor, grep in CategoryTheory/Sites/Descent, and LeanSearch for universal descent under refinement. All services answered. Their exact query text and returned log summaries are appended to mathlib_searches. Mathlib Precoverage.lean lines 49-55 and 323-327 require a topology and IsPrestack instance. The canonical fully faithful comparison theorems and definitions of pullFunctor returned by the other searches do not supply the refinement theorem under the current hypotheses in one line.

## Unfinished work

None for this one-level natural-language split. No Lean files were written and no compiler, Lake or build command was run. Only the sandbox was written.

## Review by Q112

I read delivery-errors sections B-E in both occurrences and checked the actual node against them. I compared the unchanged hypotheses to the Rydh context just described. This lemma is a supporting construction for the refinement assertion, not a claim that Rydh separately proves the stronger Hom-only statement. The proof uses arbitrary arrows and only inverts the given descent isomorphisms, so the fibres need not be groupoids and object-effectivity is never required.

Step 1 cites three statements, which I opened in full. `def-pc-fibre-product` explicitly gives existence, the universal property and functoriality, enough for W, all iterated products, projection maps, and the graph. `def-weil-quasi-separated-morphism` explicitly defines quasi-separated schemes by their structure map to Spec Z. `lem-weil-pbc-qcqs-morphism-permanence` gives exactly the three assertions needed: a morphism from a quasi-separated source is quasi-separated, base change preserves that property, and a quasi-separated morphism over a quasi-separated base has quasi-separated source. I also read Stacks schemes.tex, labels lemma-separated-permanence (Tag 01KU) and lemma-compose-after-separated (Tag 01KV), which underlie those clauses. Consequently Y, Y times_S Y, W, its kernel pair, and U times_S (Y times_S Y) are legitimate test schemes. This step's geometric input is non-elementary and is cited; it does not infer permanence from a definition alone. The subsequent Hom lifting and injectivity are exactly the universal-descent hypothesis already in the item's statement.

Step 2 defines h as an actual morphism q^*A to q^*B, with the correct direction of alpha inverse. Its notation uses maps from fibre products, not points or stalks. The pseudofunctor associativity and unit identities in the hypothesis handle parentheses; no strictification or coherence theorem is being imported. Step 3 writes the kernel-pair equation h_2=h_1 using the given compatibility of v and both cocycles, and applies the assumed Hom bijection only at V=Y. Pullback along (id,a) yields v by the diagonal identity. These are direct substitution and an application of a hypothesis, with no uncited lemma.

Step 4 compares beta f_1 with f_2 alpha on the correct overlap Y times_S Y. I checked the displayed compositions' sources and targets: both go from A at y_1 to B at y_2. On U times_S Y times_S Y they become the same expression by the two cocycles. The map to Y times_S Y is itself a base change of ba, so faithfulness follows from the stated universal-descent hypothesis at this base; it does not follow from surjectivity of a or an unproved descent statement. Step 5 derives q^*g=h directly from the datum-arrow equation and then uses the same injectivity at Y. Restriction preserves the datum equation, identities, and composition by functoriality, giving the Hom-set bijection and fully faithful functor.

For B1-B9, there are no new statement-only nodes, matches, tags or statements to validate; the item retains all inline notions and its statement dependencies. Search provenance is the exact msearch log, and citations.json quotes only actual cited statements. For C1-C4 the only external mathematical fact is the cited permanence lemma; every other displayed implication is a calculation from the hypotheses. For C5-C8 I checked duplicates and retained the unit route; proof dependencies are existing Mathlib leaves, so no off-route tool declaration or cycle through the parent is introduced. D1-D5 are met by leaving the construction, overlap equation and compatibility verification in the item rather than moving its clauses into new nodes. No step exceeds 2000 characters or hides a comparison lemma.

For E1-E7, I checked that no quasi-compactness, finite presentation, flatness, topology or nonempty-cover hypothesis is inserted. Test cases: a=id reduces the formula to the given arrow; b=id makes p=a and recovers the assumed comparison; Y=S disjoint union S with U the first component and p=id_S gives a non-surjective a and the formula still propagates to both components. For empty U or S, the argument still uses the assumed Hom bijections and never chooses a point. A constant non-groupoid fibre category reduces to conjugation of an arbitrary, possibly noninvertible, morphism; the formulas use no inverse for that morphism. These checks found no statement dispute. I corrected the potential direct-descent-along-a error by explicitly using q and checked the inverse order in the kernel-pair calculation. Nothing remains unresolved mathematically.
