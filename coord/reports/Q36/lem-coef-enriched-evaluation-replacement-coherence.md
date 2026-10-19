# Stage-1 delivery: lem-coef-enriched-evaluation-replacement-coherence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-enriched-evaluation-replacement-coherence.json`: item, statement, split. Preserved its statement; supplied six proof steps and recorded actual additional Mathlib searches. No Mathlib match.
- `citations.json`: eight step/node records, with literal extracts of the cited node statements.
- This report. No new nodes or unit edits. Zero new Mathlib leaves.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for enriched evaluation / evaluation replacement, then the category-theory sources for enriched/coherent/simplicial notions, and `dag/lean_names_upstream.json` for the notion. There is no matching declaration of the project. The master checkout likewise supplied no matching declaration; it was reference material only.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Section 1.1.5 (Definition 1.1.5.5, Example 1.1.5.8 and Proposition 1.1.5.10), and Proposition 1.2.7.3, for lem-coef-enriched-evaluation-replacement-coherence. No archived HTT file was found in literature/. Read the PDF online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf (the IAS endpoint timed out). Also read Kerodon Theorem 4.4.4.4, Tag 01DK, https://kerodon.net/tag/01DK. The proof is marked agent-written; no literature download was made. No Stacks tag states this simplicially enriched coherence assertion.

## Findings and corrections

The statement is correct; no STATEMENT-DISPUTED correction is needed. Its source lists substantial rectification/projective-model references, but this restricted conclusion only needs explicit enriched evaluation, a strict enriched interval, bifibrant localization, and pointwise equivalence detection. In particular, existence of a projective model structure cannot be inferred from the hypotheses, which allow any simplicial model category. Step 1 explicitly uses only the enriched-end definition from the projective-calculus node. It does not use that node's existence theorem, which assumes combinatoriality. No additional hypothesis was imposed.

The current blueprint ancestor proof was read in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2 before the derived coefficient-adjunction display. The item is a descendant supporting the coherent realization needed for that calculation. The chapter and the bound unit `sk-prop-sf-biduality-general` were read. Their route is retained; no realization fields or binding were changed.

Searched the entire DAG for evaluation/replacement, enriched evaluation, coherent nerve, and the pointwise criterion (including 1.2.7.3), and ran `tools/blueprint_refs.py search 'enriched evaluation'` and `search 'coherent nerve'` (both zero blueprint matches); checked the ancestor command. Reused the existing pointwise, currying and pushout-product nodes rather than creating general coherence lemmas. Read `lem-coef-enriched-nerve-transformation`: its theorem is specifically for Kan-complex targets, so it was not silently applied to the different target A^{cf}. The interval construction is instead proved directly in steps 2–3. Read `lem-coef-simplicial-derived-exponential` as a candidate and did not use its stronger, inapplicable projectively bifibrant/combinatorial hypotheses.

The inherited Mathlib searches have been retained. Additional searches were actually made through msearch.py and their outputs read: LeanSearch, Loogle, two different LeanFinder phrasings and Mathlib grep. Examined the candidate files Enriched/Basic.lean:393–461, Enriched/FunctorCategory.lean:39–95, SimplicialNerve.lean:14–34 and ModelCategory/Bifibrant.lean:194–200. The nerve file itself lists the quasicategory theorem among its projects; enriched definitions and the identity of weak-equivalence predicates do not prove the item. Ordinary nerve-edge correspondences returned by the second semantic query also do not prove it. No new node was needed.

## Not duplicates

No new nodes. No duplicate-tag pairs arise. The item is not the Kan-valued enriched-nerve-transformation node: its target is a general simplicial model category's bifibrant subcategory, with two-parameter evaluation and subsequent restriction/currying. The proof supplies these operations explicitly.

## Unfinished work

None in the one-level split. No Lean was written or compiled. The independent maintainer review remains the next project stage after delivery.

## Review by Q36

I read the item, its four statement dependencies, the chapter/unit records, the ancestor's current blueprint proof, the pointwise-equivalence node, strict currying, the inner-anodyne pushout-product node, and the candidate enriched-nerve-transformation and derived-exponential statements. I read the online HTT passages for the nerve and functor simplicial sets, and Kerodon 01DK for the vertex criterion. There are no new nodes requiring separate source comparisons.

Step 1 uses the projective-calculus statement's explicit enriched-end mapping description. I checked that the values H_j(b)(i) are the ones assumed bifibrant. Evaluation on mapping simplices is written as either order of the two-variable action. End naturality makes the orders equal, and the same interchange proves composition. This is a direct enriched-category calculation. I deliberately did not invoke existence of a model structure or objectwise preservation of cofibrancy; neither is assumed here.

Step 2 uses no external lemma: it substitutes the assumed enriched naturality of q in B and the enriched naturality of each diagram transformation q_b in I. These two equations give naturality on each complete mapping simplicial set. Checking only underlying ordinary arrows would have been insufficient, so the proof states the simplicial-level equality and the use of degeneracies of the component vertices.

Step 3 uses no external lemma: I checked the actual cross mapping map r_y e_0(f)=e_1(f)r_x and all four possible composable interval-level triples. The reverse cross mapping object is empty. This proves an enriched functor into the full bifibrant subcategory without a Kan-target theorem or an assertion that strict functor categories model derived ones.

Step 4 uses precisely the bifibrant nerve's quasicategory assertion from simplicial-model-nerve-localization and the locally Kan nerve/discrete-nerve assertions and nerve formula from coherent-nerve-comparison. B is locally Kan as required; I is never assumed locally Kan. Product preservation is proved degree by degree from the displayed functor formula, rather than inferred from a homotopy-category comparison. Strict currying supplies the actual simplicial-map bijection and its naturality; evaluating it gives exactly the edge q_b(a(k)). This verifies the claimed component, not just its isomorphism class.

Step 5 uses the statement of simplicial-model-nerve-localization, including its agreement with inclusion of bifibrant objects. The inverse localization comparison sends the given arrow to a weak equivalence inverted by localization. Applying a quasi-inverse to an inverse and its two triangles reflects equivalence. Thus the component itself, not a substituted replacement arrow, is invertible. No converse weak-equivalence detection theorem is needed.

Step 6 uses strict currying to transpose an inner horn, and the exact pushout-product assertion with the monomorphism empty -> K. Its lifting yields that Fun(K,Q) is a quasicategory. The pointwise-equivalences statement allows ANY small simplicial index, exactly as needed first for K and then for X=N_hc B in an enlarged universe. I checked both applications' target quasicategories and that their component edges are those already identified. This proves invertibility in the full outer functor category, retaining coherence in b.

I checked B1–B10: no new statements, real search calls retained verbatim, no fake leaf or attachment, unchanged original source and maintainer fields, filled blueprint provenance retained. For C1–C8 I read each cited statement (the quotes are copied directly), checked that every non-elementary theorem used is cited, and checked that the proposed dependency closures do not return to this item. There are no off-unit tool requests. For D1–D5 the main construction and its naturality/composition argument remain in the item; nothing is moved to a restatement node. For E1–E7 I checked the category of the target, exact bifibrancy assumptions, enriched rather than ordinary naturality, and the fact that no projective model structure is required. Small-case checks include empty B, I or K (the vertex criterion is vacuous), K=Delta^0 (the evaluation edge is r), I with one object (the two-variable action reduces to the B-action), identity q (the interval construction is constant in its interval factor), and a non-locally-Kan I (no use of a nerve-quasicategory assertion for I). No false edge case was found. All proof steps are below 2000 characters; the only comparison constructed inline is the elementary degreewise product bijection, and the interval check is the explicit definition plus four composition cases.

## Delivery blocker

Two sequential `deliver.py Q36 lem-coef-enriched-evaluation-replacement-coherence --no-push` invocations exited with status 1. Both server preflights reported exactly one failure: `tools/check_dag.py` could not parse the unrelated base node `dag/nodes/sec-six-functors/lem-coef-terminal-local-kan-corepresentability.json`: `Extra data: line 261 column 2 (char 29703)`. A read-only JSON parse of the shared copy confirmed that same error. This file is not part of this delivery and is outside the worker's write authorization, so it was not modified. Nothing was pushed. Both delivery processes have exited; none remains active. The complete split, report, citations and actual search log remain in this sandbox for retry after the shared JSON is repaired. The split itself has not yet received a passing final dry run.
