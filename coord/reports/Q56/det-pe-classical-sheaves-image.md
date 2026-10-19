# Worker report: det-pe-classical-sheaves-image

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-classical-sheaves-image.json`: statement node, split; exact statement retained; no exact Mathlib match. The proof now uses the existing arbitrary-scheme set-sheaf continuity and counit criteria. No new node files and no new Mathlib leaves.
- `citations.json`: one literal statement quotation for every node cited by every proof step.
- `searches.jsonl`: genuine searches made through the required launcher command, including a second semantic phrasing and a second source pattern. `prepare.py` is a sandbox-only preparation script, outside the delivery's node/report set.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, `IsClassical`, classical-sheaf names, and comparison essential-image terms found no project declaration asserting this three-way equivalence. The only `isClassical` name hit was a triangulated-generator result, which has different objects and hypotheses. The existing shared-DAG `Sheaf.AlgebraicGeometry.ProEtaleComparisonSections` records are reused as DAG results, not misreported as slopmaster2 attachments. Upstream master sorry declarations were not used as finished proofs.

## WANTED

None. Both the current blueprint and Bhatt–Scholze are available locally.

## Problems found and corrections

The imported statement is correct. No STATEMENT-DISPUTED correction is needed. Its imported proof, however, cites `lem-weil-pbc-comparison-sections` for arbitrary X although that statement begins “Let X be affine”; it also takes the counit's explicit section formula from that node's proof, not its statement. Its basis citation `lem-weil-pbc-ind-étale-basis` likewise assumes an affine base. These are C3/C4 and E1 problems in the imported proof, not counterexamples to the theorem.

I replaced those unsupported applications by existing nodes with arbitrary-scheme statements. `lem-weil-pbc-proetale-classical-continuity-sets` gives the forward continuity implication. `lem-weil-pbc-proetale-continuous-counit-sets` gives the reverse counit implication with exactly the canonical affine continuity hypothesis. These already exist and neither dependency closure reaches this item (closures inspected: 253 and 255 nodes respectively). Thus no clause was moved into a newly created node. The final implication now has `elementary: true`, and the comparison geometric morphism is an explicit statement dependency because conditions (1) and (3) name its functors and counit.

The imported item has no `chapter` or `unit` metadata. The current `dag/chapters/sec-proetale-coefficients.json` is present and was read, together with its blueprint `_section.md`; `dag/units/sk-thm-pe-classical-sheaves.json` is absent, so I read the current blueprint unit `_section.md` and proof directly. I preserved all maintainer-owned metadata. I did not invent or install a unit. The ancestor command identifies this item as its own blueprint ancestor. `blueprint.same_as` is now `[]`: the whole-blueprint searches found this exact item, its broader parent theorem, and definitions, not another equivalent three-way statement. The parent additionally states the module equivalence and is not listed as a duplicate theorem.

The two generic tool uses are declared in `split_report.tool_uses`. They implement the same affine-continuity/counit route as the unit's existing proof, without replacing a unit step by a different argument. I did not set the maintainer's `tool_uses` field. All original `blueprint_*` fields and import flags are preserved.

## What remains unfinished

No mathematical part of the split remains. The second reader must independently check it and deliver it; this worker does not push.

## Not duplicates

No new nodes. Before deciding to create none, I searched the entire DAG by comparison/counit/continuity terminology and relevant tags, and ran `tools/blueprint_refs.py search` for comparison, classical, classical continuity, affine-basis, and essential image comparison. The general comparison-continuity and continuous-counit results already exist, so creating either as a new node would violate the duplicate rule.

## Review by Q56

I read `coord/brief-stage1.md`, `stages/1-dag.md`, SETUP's three levels, GOAL, the sync contract, and delivery-errors B–E in full. For the item I compared the current `main-20261015` statement and its three proof paragraphs with Bhatt–Scholze, *The pro-étale topology for schemes*, Lemmas 5.1.1–5.1.2 and the observation after Definition 5.1.3, printed p. 34. Lemma 5.1.1 is the affine presentation evaluation formula; Lemma 5.1.2 identifies the essential image by continuity and explicitly derives the inverse counit. This is the source route of the delivered proof. I also read Stacks `proetale.tex`, Tag 0GLZ (`lemma-describe-pullback-from-etale`) and Tag 099S (`lemma-limit-pullback`), confirming that the general comparison and limit statements are for arbitrary schemes and sheaves of sets. They are corroboration here, not uncited lemmas used by our proof. No SGA source is used.

For step 1 I opened the full statements of `det-pe-classical-definition-continuity-map` and `lem-weil-pbc-proetale-classical-continuity-sets`. The first requires bijectivity of the restriction-induced map for every affine étale presentation, and the second states preservation of filtered colimits on the opposite affine ind-étale site for any scheme X and any étale set sheaf. A cofiltered affine étale presentation becomes just such a filtered section diagram: the geometric transition maps and the projections are exactly those in the definition. No affineness of X, finiteness of a coefficient ring, constructibility, or noetherian hypothesis is added. I wrote the actual naturality square for the isomorphism G ≅ ν_X^*F. Its componentwise inverses induce an inverse on the colimit, so the continuity map for G is bijective. This is elementary transport after the cited continuity theorem, not an extra lemma hidden behind the word “invariant”.

For step 2 I opened `lem-weil-pbc-proetale-continuous-counit-sets` and checked its whole statement: it assumes a scheme X, a pro-étale sheaf of sets F, and continuity for every affine ind-étale presentation by affine étale X-schemes; it concludes invertibility of precisely ν_X^*ν_{X,*}F → F. With F = G, its hypothesis is condition (2) under the cited continuity-map definition. The step identifies the cocone maps with restrictions, rather than using an arbitrary bijection between sets. The cited node's statement itself gives the counit criterion, so I use none of its internal proof constructions as an unadvertised interface. It is an existing reusable theorem; no newly created node restates this clause. Both non-elementary steps are marked false for `elementary`.

For step 3 I opened `def-weil-pbc-site-comparison-morphism`, whose statement explicitly supplies the set-sheaf adjunction for every scheme. Its right adjoint sends G to an étale set sheaf. Setting F = ν_{X,*}G and taking the inverse of the assumed counit isomorphism proves condition (1) in one line. This step is correctly elementary and does not need full faithfulness or a new category-theory lemma. The definition is being used for its functors and their types, not for an unstated section theorem.

For B1–B9 there are no new-node obligations: no new data definitions, no unsupported self-contained statements, no new Stacks tags, no leaf declarations with missing line numbers, and no orphaned statement-only nodes. Existing references are genuine exact interfaces. The item's Mathlib searches were all run through `msearch.py`; the results are recorded from the search log with the identical tool and query text. I read the returned hits: condensed/light-condensed essential-image characterizations concern a different site, generic dense-subsite equivalences do not supply the pro-étale continuity hypothesis, and the other hits are scheme/site constructions or affine-limit geometry. The second semantic query likewise did not produce the three-way pro-étale statement. LeanSearch, LeanFinder, Loogle and both source searches succeeded; no unavailable query is represented as a negative result.

For C1–C8, each non-elementary step cites the theorem that states its whole required fact; the final witness and the isomorphism-transport square are written out. Every step's node citation has a verbatim quotation in `citations.json`. The union of `uses` is exactly `proof_deps`. I traversed the statement/proof dependency closures of the two tool results and the comparison-unit theorem to rule out an implicit cycle back to this item. I retained the unit's continuity/counit route and explicitly declared the two external tool uses.

For D1–D5, the three implications are actual arguments using pre-existing results; there is no relabelling, no new node containing the whole equivalence, no circular induction and no unresolved “details omitted” in this item's proof. The underlying continuity/counit subproofs belong to their existing nodes; they have not been silently imported from another node's proof text.

For E, I tested the empty scheme (sheaf values on the empty object are singleton sets and the same adjunction argument applies), a constant one-stage affine étale presentation (the continuity map is the identity), the terminal sheaf (all continuity maps are bijections), and the transport square with an arbitrary chosen sheaf isomorphism and its inverse. The nonclassical case is not wrongly identified with all pro-étale sheaves: step 2 explicitly requires the canonical continuity map to be bijective. Crucially X may be nonaffine, non-quasi-compact, or non-quasi-separated throughout; the two selected theorem statements require none of those properties. There are no new statements for which further small-case testing is needed.

The corrections made during this review are the affine-base citation repair, removal of the unsupported appeal to a cited node's internal counit construction, insertion of the explicit isomorphism-transport argument, addition of the comparison statement dependency, and completion of the elementary/source/blueprint/search fields. The three-condition statement was kept exactly as imported.

## Resumed audit, 2026-10-16

The present worker reopened the preserved split, the unchanged imported statement, all four cited node statements, both rejected affine-only interfaces, the current chapter record, and the current blueprint unit and its image proof. Bhatt–Scholze printed p. 34 was read directly with pdftotext, and Stacks Tags 0GLZ (`lemma-describe-pullback-from-etale`) and 099S (`lemma-limit-pullback`) were read in `proetale.tex`. The item remains imported in the shared snapshot. The continuity and counit interfaces apply to arbitrary schemes and sets exactly as the three steps require. All five quotations are verbatim parts of the current statements. Full statement/proof dependency traversals found no path back to this item (closure sizes 70, 253, 255 and 84 for the four cited nodes).

The preserved `searches.jsonl` contains the actual msearch invocations recorded in the node. I checked the generic adjunction hits `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage` and `CategoryTheory.Adjunction.mem_essImage_of_counit_isIso` in `Mathlib/CategoryTheory/Adjunction/FullyFaithful.lean`, lines 202–213. They give only the formal counit/essential-image implication, not the affine-continuity characterization, so the item is not a Mathlib leaf. The Proetale site file supplies the site construction, not this theorem. Repeated project-source searches for the exact blueprint tag, item id, classical-sheaf names and comparison essential-image terms found no attachment.

This resumed audit changed only this report: removed obsolete claims about previous second readings and corrected the now-present chapter record. The mathematical split, citation quotes and genuine search records remain intact. The report is the worker's self-review; a fresh second reader must still review and deliver. No new nodes, Lean writes, compiler calls or push were made.

## Dry run

Validation uses the required `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q56 det-pe-classical-sheaves-image --no-push`. Earlier rounds encountered shared fetch/worktree locks; historical success/failure messages do not substitute for this resumed run. The worker issues READY only when this run prints OK (not pushed). No delivery push is authorized for this worker.

## Second reading by Q56

- Item statement: checked verbatim against the blueprint node `det-pe-classical-sheaves-image` and the three conditions in Bhatt–Scholze, Lemma 5.1.2; all hypotheses are exactly “scheme $X$” and a sheaf of sets on $X_{\Proet}$, with no affine or finiteness restriction.
- Step 1: checked against `det-pe-classical-definition-continuity-map` and the full statement of `lem-weil-pbc-proetale-classical-continuity-sets`; the latter applies to arbitrary schemes and its filtered-colimit preservation gives the canonical restriction cocone, while the displayed naturality square supplies the isomorphism transport. Verdict: sound, non-elementary, citations quoted verbatim.
- Step 2: checked against the definition's canonical restriction cocone and the full statement of `lem-weil-pbc-proetale-continuous-counit-sets`; its hypotheses match classicality for every affine ind-étale presentation and its conclusion is exactly the counit isomorphism. Verdict: sound, non-elementary, no affine hypothesis imported.
- Step 3: checked against `def-weil-pbc-site-comparison-morphism`; its adjunction types $ν_X^*$ and $ν_{X,*}$ as sheaf functors, so taking $F=\nu_{X,*}G$ and inverting the assumed counit proves (1). Verdict: sound and elementary.
- New nodes: none; therefore B1–B7 and new-node small-case checks are vacuous. Existing tool nodes were read in full, and their statements (rather than proof text) are the only facts used.
- Source and edge cases: read Stacks `proetale.tex` Lemmas `lemma-describe-pullback-from-etale` and `lemma-limit-pullback`, plus the blueprint proof and Bhatt–Scholze p. 34; checked the empty scheme, a constant one-stage affine presentation, the terminal sheaf, and transport by an arbitrary sheaf isomorphism. No statement dispute found.
- Changes made in this second reading: none to the mathematics; the prior repair's arbitrary-scheme tool citations, explicit transport square, comparison dependency, citations, and search records were retained. Added this independent review and then reran the required dry-run delivery, which passed preflight.
