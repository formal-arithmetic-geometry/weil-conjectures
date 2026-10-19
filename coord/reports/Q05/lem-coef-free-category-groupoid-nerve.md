# Stage-1 report: lem-coef-free-category-groupoid-nerve

## Files written

- `dag/nodes/sec-six-functors/lem-coef-free-category-groupoid-nerve.json`: statement, unchanged; split into seven steps.
- `dag/nodes/sec-six-functors/lem-coef-free-product-nerve-gluing.json`: one new statement, unsplit; no Mathlib match after two LeanFinder phrasings, Loogle, LeanSearch and source grep. This is Dwyer–Kan I, Lemma 3.8, for arbitrary factors on the same object set.
- `citations.json`: eight step/node entries with verbatim portions of the cited statements.
- `report.md`: this report. Search output is also retained under `work/search-results.json`; actual searches were recorded by msearch.py in `searches.jsonl`.

There is one new node and zero Mathlib leaves. No Lean was written, no compiler/build was run, and the shared repository, source checkouts and launchers were not modified.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, free groupoids, groupoid completion, path categories, and the free-product/nerve comparison returned no matching declaration. The item has no `lean_audit` field and no recorded declaration to attach. The sorry declarations of upstream master are not used as proofs.

## WANTED

WANTED: Dwyer and Kan, *Simplicial localizations of categories*, Journal of Pure and Applied Algebra 17 (1980), pp.267–284; Sections 1.4, 2.1–2.3, 2.8–2.9 and 3.1–3.8, especially Proposition 3.7 and Lemma 3.8, for the item and `lem-coef-free-product-nerve-gluing`. The paper is not in the local literature inventory. I read the primary-source PDF at `https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf`; I did not download into the read-only repository. Its local archive remains wanted. The item's proof is marked agent-written, with its current-blueprint ancestor as provenance and the online source identified explicitly.

The existing citations retain their own source/archive qualifications. No Stacks tag states the free-product nerve lemma or the free-category inversion theorem, so no Stacks tag is invented for either. Stacks 04AZ specifies cofilteredness only; the existing filtered-nerve node states the additional topological theorem actually used.

## Problems found and repaired

The imported item had an empty proof. Its statement and its source attribution to ordinary free categories are correct and are unchanged. In particular, I did not replace it by Dwyer–Kan Proposition 9.2 for cofibrant simplicial categories. There is no STATEMENT-DISPUTED finding.

Proposition 3.7 has a very compressed proof: it reduces to the one-generator case and refers to free-product decompositions and Lemma 3.8. I expanded the one-generator cases, including a loop, the finite induction and the infinite edge-set passage. The nontrivial free-product nerve inclusion is now a named dependency, rather than being called elementary. It must apply to arbitrary factors, because the second use in the induction is on groupoids, which are generally not free categories. The statement of the new node includes that generality.

Only the item's own proof and search/split metadata were changed. Its chapter/unit binding and inherited blueprint ancestry were retained. The current main-20261015 blueprint proof's second paragraph is the mapping-limit calculation served by that ancestry; there is no change of route. This item is not a unit's key statement, so no unit realization file is delivered.

## Not duplicates

`lem-coef-free-product-nerve-gluing` vs `lem-coef-free-category-groupoid-nerve`: the new node compares a simplicial pushout with the nerve of a categorical coproduct for two arbitrary categories. It contains neither groupoid completion nor inversion; it supplies both horizontal comparisons in the item's induction, whose vertical map is proved using separate input.

`lem-coef-free-product-nerve-gluing` vs `lem-coef-fixed-object-simplicial-free-calculus`: the existing statement gives mappingwise invariance of free products of simplicial categories and a fixed-object model structure. It does not compare a pushout of ordinary nerves with a nerve of a free product.

`lem-coef-free-product-nerve-gluing` vs `lem-coef-free-factor-hammock-comparison`: the existing statement concerns mapping spaces of a hammock localization of a free pair. It states neither a free-product nerve inclusion nor the conclusion used in the present proof.

`lem-coef-free-product-nerve-gluing` vs `lem-coef-sset-gluing-filtered-equivalences`: the existing statement concerns weak equivalences between pushouts of spans and filtered colimits. It does not identify the homotopy type of a categorical free product. The item uses both results for different arrows of the commuting square.

The whole DAG was searched by the actual statements for free categories, free groupoids, free products/amalgamation and nerve comparisons, including nodes outside the target reach. Whole-blueprint searches using `tools/blueprint_refs.py search` for `free category`, `free product`, `groupoid`, `amalgamat`, `comma` and `nerve` found no duplicate statement; searching Theorem A led to generic results but no free-product comparison. The existing aspherical and filtered-nerve nodes were reused instead of creating copies. There is no shared Stacks tag for the new node.

## Review by Q05

I read Dwyer–Kan I, Sections 1.4, 2.1–2.3, 2.8–2.9 and 3.1–3.8, pp.269–273, with the PDF open at Proposition 3.7 and Lemma 3.8. The new node is precisely Lemma 3.8, expressed as a pushout along the discrete nerve instead of the displayed union. The two factor nerves meet on identity strings, which explains that reformulation. I checked that the source assumes small categories with the same object set, not connected or nonempty categories, and does not require either factor in Lemma 3.8 to be free. I also read the current main blueprint ancestor's statement/proof and the assigned chapter/unit records. No SGA source was used.

For step 1 I checked directly from the definitions that all categories are small and that the zero-edge map is the identity. Keeping all vertices, even outside the support of a finite edge set, is necessary: otherwise the later span comparisons would change the discrete object set. This step is elementary and uses no external theorem.

For steps 2 and 3 I opened and read the complete statements of `lem-cbc-filtered-nerve-weak-contractibility` and `lem-coef-grothendieck-aspherical-base-change`. The former really concludes weak contractibility of the nerve of a small nonempty ordinary filtered category, and the latter really includes the nerve implication of Quillen's Theorem A; I do not use its proof or infer this from a definition of asphericity alone. I also checked the primary-source Theorem A in Low arXiv:1409.8062, Definition 1.7 and Theorem 1.9, and the filtered-contractibility reference Kerodon 02PH. The comma orientation is explicitly `(b downarrow u)` with relation `u(h) alpha = alpha'`. For a non-loop edge the comma category is the walking arrow, with a common successor at its target. For a loop it is the full ordered set of integers, not the natural numbers: a comma object is an arbitrary integer arrow of the completed groupoid, and its forward arrows correspond to nonnegative differences. It is nonempty, pairs have a maximum, and parallel arrows are equal. Isolated vertices yield singleton comma categories. These checks establish every smallness, nonemptiness and filteredness hypothesis used.

Step 4 uses only the presentations and gives the actual inverse maps identifying completion with a free product of groupoid factors. I checked composition and inverses on generators and signed words; I do not cite a construction node for an unrecorded preservation theorem. This is an elementary universal-property calculation, kept as a proof step rather than manufactured into a node.

For step 5 I read the complete statements of the existing simplicial gluing node, the new Lemma 3.8 node and `lem-coef-kan-quillen-right-proper`. The simplicial gluing statement requires monomorphisms on the two specified legs, and the proof checks this degreewise using identity strings. The three vertical span maps are the induction hypothesis, the identity and the one-generator map, all genuine weak homotopy equivalences. Lemma 3.8 supplies each horizontal map separately. Naturality needed for their square is immediate from their definition as canonical maps out of pushouts; the proof checks the equality on both factors. The final inference uses composition and two-out-of-three from the cited model structure. The induction names its claim, its empty base case and a strictly smaller finite edge subset, so there is no circular invocation of the desired result. The smallness and fixed-object-set conditions hold for both category pairs; crucially no freeness condition is assumed in the groupoid pair.

In step 6 I checked the degreewise colimit identifications using explicit representatives. Surjectivity needs only the finite number of edges in a finite string of finite words. Injectivity on the groupoid side requires a finite derivation of an equality in a presentation; I wrote that argument instead of assuming an unproved preservation theorem for the nerve or assuming all transition maps injective. Every relation in such a derivation involves finitely many letters, so a single finite subset witnesses it. The face and degeneracy maps respect these identifications. Step 7 cites exactly the existing node's filtered-poset colimit clause. The poset is small and nonempty and finite unions give upper bounds; no hidden countability or monomorphism hypothesis is imposed. This identifies the resulting map with the actual canonical localization map, not just an abstract equivalence between the two spaces.

I tested the statement on the empty graph on the empty set, a discrete graph with isolated vertices, a single arrow between distinct vertices, a single loop, two parallel arrows, and a pair of oppositely directed independent generators. The loop case explains why replacing all one-generator nerves by contractible spaces would have been false; the proof instead uses Quillen's Theorem A for its map. Multiple edges stay distinct in the finite subsets, so parallel edges do not collapse. Infinite edge sets use the full finite-subset poset, which always includes the empty subset. For the new lemma I checked empty object set, either factor discrete, and two one-object factors: the conclusion is a weak equivalence of a wedge-shaped nerve pushout, not a false strict preservation of coproducts by the nerve.

Against delivery-errors B–E: the new unsplit node has only a self-contained statement, no proof sketch or proof dependencies; all its notions are defined inline or supplied by its stated dependency. Sources and places are explicit and no inaccurate Stacks tag or Mathlib leaf is claimed. Each recorded new-node search really ran through msearch.py; I read its hits and inspected Mathlib `FreeGroupoidOfCategory.lean:14-145`, `Nerve.lean:50-125`, `NerveAdjunction.lean:373-410`, and `CechNerve.lean:185-222`. The results construct free groupoids, truncated nerve adjunctions and Cech conerves, not the homotopical theorem needed. Elementary presentation/finite-support calculations remain steps. The only new node is a separate general categorical pushout comparison, not a clause of the item. Every non-elementary step cites the theorem it uses; all eight citations have verbatim statement witnesses in citations.json. I checked that none of the reused dependencies has a path back to this item. The sole off-unit theorem is the generic filtered-nerve criterion, declared in `split_report.tool_uses`; its application does not substitute a new geometric route for the unit's route.

## Unfinished work

The one new statement-only node is intentionally unsplit for the next stage-1 item; its source is Lemma 3.8, whose proof passes through the free-category spine theorem 2.9 and the standard free simplicial resolutions. The present item's proof uses its statement only. All requested work on the assigned item is prepared for the second reader. The mandated no-push dry run is the final acceptance check; no delivery push is authorized for this worker.

## Second reading by Q05

- Item statement: checked against Dwyer--Kan I, Proposition 3.7 (printed p.272), including arbitrary small vertex set, loops, multiple edges, and isolated vertices; verdict: agrees.
- Step 1: checked against the free-category and groupoid-completion presentations in Sections 1.4, 2.1, 2.3, and 3.1--3.2; empty-edge and empty-vertex cases are explicit; verdict: elementary and sound.
- Step 2: checked against the complete statements of `lem-cbc-filtered-nerve-weak-contractibility` and `lem-coef-grothendieck-aspherical-base-change`, with the non-loop comma categories calculated for both endpoints and isolated vertices; verdict: cited conclusions apply.
- Step 3: checked against the same two dependency statements and the signed-word presentation in Section 3.2; the loop comma category is $(\mathbb Z,\leq)$ and is filtered; verdict: cited conclusions apply.
- Step 4: checked against the universal-property presentations in Dwyer--Kan Sections 2.2--2.3; the inverse maps on generators and formal inverses are written; verdict: elementary.
- Step 5: checked against `lem-coef-sset-gluing-filtered-equivalences`, `lem-coef-free-product-nerve-gluing`, and `lem-coef-kan-quillen-right-proper`; finite induction, monomorphism hypotheses, naturality, and two-out-of-three are all stated; verdict: dependencies say what is used.
- Step 6: checked degreewise against the finite-word presentations in Sections 2.1 and 3.1--3.2; finite supports and finite equality derivations justify both colimit identifications; verdict: elementary.
- Step 7: checked against the filtered-poset colimit clause of `lem-coef-sset-gluing-filtered-equivalences`; the finite-subset poset is nonempty and directed, including empty edge and vertex cases; verdict: cited conclusion applies.
- New node `lem-coef-free-product-nerve-gluing`: checked against Dwyer--Kan I, Lemma 3.8 (printed pp.272--273), with empty object set and discrete-factor cases; verdict: self-contained statement-only node, no duplicate found.

I changed no mathematical statement or proof step. I added this second-reading record after checking every citation quote, all B--E requirements, the whole-DAG duplicate searches, and the recorded Mathlib searches. The only delivery preparation change is this report section; the worker's one new node remains unsplit by design.
