## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lifted-generator-quasiseparated-test.json`: statement; now split into four proof steps. The statement, statement dependencies, original provenance and original search records are retained. Five actual Mathlib searches from this run were appended; no match.
- `citations.json`: one verbatim statement quote for every step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, lifted generators, coherent topoi, quasi-compact topos objects and generator-cover terminology found no project declaration stating the item. The scheme and site cohomology declarations found do not give this topos-object theorem. There is no Lean audit entry in the imported item requiring an additional attachment.

## WANTED

None. The proof is an agent argument using the existing DAG calculus and definitions, rather than a claimed verbatim theorem in a missing reference.

## What was wrong or incomplete

The live item had no proof or proof dependencies. Its two assertions are correct as written, including empty finite covers and arbitrary (possibly non-quasi-compact, non-quasi-separated) P and A. I changed no statement and found no statement dispute.

The source's Stacks tags are ingredients, not a source theorem with this exact statement. I read `literature/stacks-project/sites.tex`, Tag 0D07 (`definition-quasi-compact-topos`), Tag 0GMP (`lemma-image-of-quasi-compact`, especially its sheaf-object assertion), and Tag 0GMQ (`lemma-coproduct-quasi-compact`). The last tag states the nonempty finite case; the existing `lem-trf-topos-finite-cover-calculus` statement explicitly supplies the empty case as well. The source's local-lifting and pullback ingredients are already encapsulated in that same node, so I did not create or inline another sheaf-theoretic theorem.

I also read the local ILO PDF, Exposé XI, Lemma 2.5 and its proof, printed pp. 178–179 (PDF pp. 184–185). This explains the finite-limit-closed coherent generating subcategories and finite-cover coherence context. It does not purport to state the present auxiliary. The item's proof_origin is therefore `agent`.

I read the recorded chapter/unit and the latest blueprint ancestor `lem-trf-local-term-locality` and current `sk-i-curve-zero/_section.md`. The current ancestor treats contracting correspondences; the item is an auxiliary in the already recorded constructibility/coherent-topos dependency chain, not a replacement proof of the local-term theorem. Its existing blueprint provenance is retained. No chapter or unit file is changed, and this item is not the unit's key statement. Searches of the whole imported blueprint by `blueprint_refs.py` for lifted generators, coherent topoi, finite generators, generator covers and quasi-separatedness, together with DAG keyword/tag searches, found no exact blueprint duplicate of the item.

## Not duplicates

No new nodes were created. In particular, the tag search for 0GMP/0GMQ led to the existing `lem-trf-topos-finite-cover-calculus`; its clauses (1) and (3) are exactly the generic cover and compactness facts used here. I reused it rather than introducing finite-product-cover, pullback-epimorphism or finite-cover-descent nodes. `lem-trf-sheaf-quasicompact-coproduct-calculus` concerns coherent coproducts and summand pullbacks, and `lem-trf-coherent-generator-subobject-closure` concerns finite-limit closure; neither needs to be added to this proof. The already split parent `lem-trf-coherent-epimorphic-quotient` depends on this item and was not cited, avoiding a cycle.

## Mathlib searches

All five searches in this run used the required `msearch.py NO lem-trf-lifted-generator-quasiseparated-test` command and are recorded in `searches.jsonl` and appended verbatim as query/tool pairs to the node. Both natural-language formulations were read. LeanFinder returned coherent-topology sheaf conditions, finite presheaf generation, condensed local-surjectivity and scheme/topological cover results. LeanSearch returned scheme quasi-separatedness. Loogle returned `CategoryTheory.isSeparator_iff_epi`, whose source I read at `Mathlib/CategoryTheory/Generator/Basic.lean:660`: it gives an arbitrary coproduct generator criterion, without finite selection or either quasi-separatedness implication. The grep found finite subpresheaf generation at `Mathlib/CategoryTheory/Subfunctor/Finite.lean:73`; I read that interface and the epimorphism result at line 154. These concern finite generation of presheaves, not quasi-compact objects in an arbitrary sheaf topos. I also read the scheme quasi-separatedness interface at `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:50` and its diagonal criterion at line 197. It is restricted to schemes and does not specialize to this statement in one line. No service was unavailable. There are no new nodes requiring separate searches.

## Unfinished work

None in this stage-1 split. The proof of the existing cited cover-calculus node remains that node's independent stage-1 task; this delivery does not assert it is already proved in Lean.

## Review by NO

I checked the split against delivery-errors B–E with the item, both cited node statements and the local sources open. No definition, statement-only lemma or restatement of a clause was created. The four proof steps have respectively 801, 369, 774 and 656 characters, so none hides an argument inside a step over 2000 characters. Each step writes the actual maps and their equations rather than saying only that the result descends or follows from locality.

Step 1 uses the quasi-compactness definition in `def-trf-coherent-topos`. The generating hypothesis in the item supplies a small cover of E. I explicitly checked right cancellation twice to prove that its composite with e covers X; finite selection is then exactly the definition, and retaining the original maps retains the lifts. Applying this to the identity of X proves the last assertion of (1). The step is elementary because it is the two cancellation implications and an application of the definition; it does not assume generators are projective or that the cover of E is finite.

Step 2 uses the same definition node: coherent implies quasi-compact, and quasi-separatedness quantifies over all pairs of quasi-compact sources. Thus it really applies to K and L with maps pk and pl. This implication is elementary and does not use p's epimorphy.

For step 3 I read the statement, not the proof, of `lem-trf-topos-finite-cover-calculus`. Clause (1) explicitly states that epimorphisms remain epimorphisms after every pullback. Its application to p along b and c therefore has all hypotheses, without a finiteness condition on P, A or the two pullbacks. The finite lifted-cover result used next was proved in step 1 of this very item. Projecting its lifts to P yields the equations pk_i = bs_i and pl_j = ct_j by the pullback universal property. I checked that it is B and C that are assumed quasi-compact; neither B×_A P nor C×_A P is inadvertently assumed so.

Step 4 uses the exact product-family assertion in clause (1) of that existing calculus node: two jointly epimorphic families over B and C induce the stated family over B×_A C, for arbitrary maps B,C→A. The equations from step 3 identify the A-maps in the test with those in this product family. The test supplies quasi-compactness of each source, and clause (3) explicitly states the finite jointly epimorphic quasi-compact-source criterion, including the empty coproduct. The final use of `def-trf-coherent-topos` is exactly its quantified definition of quasi-separatedness. All non-elementary cover and compactness facts in steps 3–4 are thus supported by the cited statement. `citations.json` copies the full statements verbatim so no proof-only claim is passed off as a statement quotation.

I tested the edge cases in Set, a coherent topos with finite sets as coherent generators: the empty target admits the empty family; a surjection from an infinite P to a finite target still permits a finite lifted cover; and an infinite A (even with infinite P) is quasi-separated because fibre products of two finite sets are finite. Thus the reverse implication must not accidentally demand compactness of A. If either B or C has an empty selected cover, the cited empty-family assertion still gives the required quasi-compact fibre product. The proof also covers a degenerate topos because it never demands a nonempty cover. Index sets are the small generating family supplied by the hypothesis, its finite subsets and their finite Cartesian product, all within the stated containing universe.

No off-unit tool is used: both proof dependencies have unit `sk-i-curve-zero`. The size convention remains a statement dependency. The chapter and unit routes, target statements and unrelated nodes are untouched. The substantive repair was to supply the absent proof using the existing generic calculus, without manufacturing another node for either clause.
