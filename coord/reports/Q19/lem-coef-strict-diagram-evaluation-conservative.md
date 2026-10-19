# Q19 stage-1 report

1. Files written: `dag/nodes/sec-six-functors/lem-coef-strict-diagram-evaluation-conservative.json` (split; statement unchanged); `dag/nodes/sec-six-functors/lem-coef-localization-homotopy-category.json` (one new statement-only unsplit node; no Mathlib match); `citations.json` (verbatim statement quotations for every use). Sandbox scripts and the search log are not project files.
2. Attachments: none. Searches under the read-only `WeilConjectures/` tree for the exact item id and evaluation/conservativity concepts found no declaration stating this theorem. Upstream-master sorry declarations are not attachments.
3. WANTED: Cisinski, *Higher Categories and Homotopical Algebra*, https://cisinski.app.uni-regensburg.de/CatLR.pdf, Theorem 1.6.6, Corollary 1.6.8, Remarks 7.1.4 and 7.1.6, and Theorem 7.9.8, for this item and its comparison prerequisite. Read online on 2026-10-17; not downloaded into the repository. There is no relevant Stacks tag for these quasicategorical assertions. The proof is marked agent-written, with the inherited blueprint ancestor as provenance.
4. The imported statement is sound and unchanged. The earlier attempt was blocked by a cycle through the existing saturation theorem and its model-definition dependency. This repair removes that citation, without editing any existing dependency or creating a duplicate saturation lemma. Steps 6–8 instead apply the existing acyclic Mathlib leaves `lem-coef-model-localization-map-surjective` and `lem-coef-localized-good-homotopy-test`, with explicit componentwise replacement, cylinder lifting, and retract calculations. No hypotheses, coefficient categories or base-change maps are changed.
5. The split is complete and the required server dry run passed. No push is requested or performed. The second reader is responsible for eventual delivery.

## New nodes

- `lem-coef-localization-homotopy-category`: ordinary homotopy category of a general full coherent localization, essential surjectivity, naturality, and the criterion for equivalence edges. It introduces its objects and the homotopy-category convention inline, and cites the existing enhanced-diagrams definition for simplicial terminology. It is statement-only and unsplit. It is independent of model categories and evaluation, and does not carry a clause of the item in disguise.

## Mathlib searches

The existing attempt's genuine `searches.jsonl` was retained. I ran additional leanfinder, loogle, grep and leansearch queries through the required msearch command, and appended the exact logged queries/results to the new node. Earlier logged queries already include a second semantic phrasing. Derived-category ordinary localizations and model-category homotopy quotients are not the coherent-localization comparison. Mathlib's nerve/homotopy-category adjunction is useful infrastructure but does not state the entire new result. The refined quasicategory grep found no localization comparison. The Loogle query with `CategoryTheory.Localization` reported an unknown identifier and no hits; its record explicitly says that query is inconclusive, not evidence of absence. No unavailable service is recorded as a negative search.

The two newly used dependencies are existing Mathlib leaves, not new nodes. I read their node statements and their pinned source: `FundamentalLemma.lean:65–134`, especially map-surjectivity at 116 and equality at 129; `Homotopy.lean:100–119` supplies the specified good-cylinder/path version. The source and target assumptions are precisely cofibrant and fibrant.

## Not duplicates

lem-coef-localization-homotopy-category vs lem-coef-pointed-model-stability: the existing statement concerns stability of a pointed model localization, not the homotopy category of an arbitrary coherent localization.

lem-coef-localization-homotopy-category vs lem-coef-model-localization-homotopy-classes: the latter computes ordinary localized Hom sets between cofibrant/fibrant objects; it does not compare arbitrary coherent and ordinary localizations.

lem-coef-localization-homotopy-category vs lem-coef-system-localization-universal: that node gives existence and finite-product preservation of localization for infinity categories with systems of arrows; it does not state the homotopy-category comparison.

lem-coef-localization-homotopy-category vs lem-coef-hammock-infinity-localization: that theorem identifies the hammock/coherent-nerve presentation of relative ordinary categories, including mapping spaces; it does not state the homotopy-category comparison and is a cyclic dependency here.

lem-coef-localization-homotopy-category vs lem-coef-localized-good-homotopy-test: the existing leaf identifies ordinary localized equality with cylinder/path homotopy under cofibrancy/fibrancy, and has no general coherent-localization assertion.

Whole-DAG searches for ordinary localization and homotopy-category comparisons, and blueprint searches for `homotopy category localization` and `coherent localization`, found no duplicate. Ancestry was checked with `tools/blueprint_refs.py ancestor`; the new node prepends this item to its inherited via chain. No Stacks source tag is introduced, so there are no same-tag duplicate pairs.

## Review by Q19

I read delivery-errors B–E, the worker and stage contracts, the three blueprint levels in SETUP, GOAL and dag-sync, the chapter and unit records, the item, and the statements cited in all ten proof steps. The unit is general biduality, with no internal steps recorded; the imported ancestry places this tool below the coefficient mapping calculation. The chapter/unit route is retained. I checked the online Cisinski material at printed pp. 24–25 and 324–325 for the new comparison node, and pp. 408–410 for the item's conservativity input. The item uses the fraction-and-detection argument preceding (7.9.8.7), without using the rectification conclusion it supports. No SGA source is cited.

Step 1 cites precisely the left lifting-class closure statement, which gives identities, composition and pushouts. The right-class pullback and composition arguments are written explicitly, not attributed to a clause absent from that node. Functorial replacement supplies strict diagram maps. Step 2 uses only those facts and the input model axioms: factoring a weak equivalence gives a trivial first factor by two-out-of-three; a pushout remains cofibrant; a pullback of a trivial fibration becomes cofibrant only after applying Q. This last correction is retained from the earlier attempt. No properness is used.

Step 3 spells out the induction on finite localization words. I checked the sources/targets in the two square completions, the equality vt=fp, the equality ku=jg, and the resulting word X<-P->H<-Z. They give the displayed inverse algebra for composition. The generators, inverses and empty word are included. This is an explicit elementary finite calculation, not a new unproved fraction lemma.

Step 4 uses the new node's essential surjectivity and ordinary-localization comparison to represent the actual homotopy class after endpoint conjugation. Step 5 uses its naturality and the input universal property to map B to the nerve of the ordinary localization H. Evaluating the fraction then makes gamma(f_i) invertible. No saturation theorem is smuggled into that step.

Step 6 applies map-surjectivity only after the specified fibrant replacements. Because f_i already has cofibrant endpoints, RA and RB are bifibrant, and E is both cofibrant and fibrant. Thus the cited leaf really represents gamma(p)'s inverse by s:RB->E. Step 7 constructs good cylinders by fold-factorization and good paths by diagonal-factorization, satisfying the exact good-homotopy-test statement. The lift has left map e0 in C intersect W and right map p in F. Its endpoint t satisfies pt=1. Step 8 applies the same existing leaf to tp and 1_E; the source E is cofibrant and target E fibrant. The two-out-of-three deductions give tp in W. I checked both arrow-retract squares (1_E,t) and (1_E,p), including their composite (1_E,pt). This recovers p, Ru, and finally f_i in W. These three steps contain the needed argument themselves and introduce no saturation node. They repair the old graph obstruction using existing smaller leaves with different, acyclic definition dependencies.

Step 9 now inverts all three fraction factors and uses exactly the new node's equivalence-edge criterion. Step 10 uses the componentwise transformation criterion verbatim from `lem-cbc-enhanced-functor-cone-calculus`. That generic off-unit tool use is declared in split_report. For empty I, the ordinary diagram category is terminal, and the comparison node makes its localized homotopy category terminal; hence the vacuous condition correctly detects every arrow. The singleton, discrete and arrow categories, and categories with automorphisms, require no extra hypothesis: strict pointwise constructions remain functorial. Testing W equal to isomorphisms gives ordinary pointwise detection; W equal to all arrows gives the expected equivalence-only conclusion. The new comparison node also passes C empty, C terminal and W all arrows. It does not assert that a coherent localization is the nerve of its homotopy category.

I checked B1–B10: the new node is self-contained, statement-only, properly sourced and searched, with exact ancestry; no Mathlib leaf is invented. C1–C8: every non-elementary input is a cited statement, every quotation in citations.json is copied verbatim, and the cyclic saturation/homotopy-class nodes are absent from proof_deps. D1–D5: the fraction induction and component lifting/retract argument remain in the parent, with one strictly independent general prerequisite. E1–E7: model hypotheses, universes, endpoints, empty shape, and all lifting squares were checked as described. No statement dispute was found. No live file, launcher, Lean file or compiler was touched.

## Dry run

Ran `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q19 lem-coef-strict-diagram-evaluation-conservative --no-push` on 2026-10-17. It printed `OK (not pushed) deliver/Q19/lem-coef-strict-diagram-evaluation-conservative at 0cca3bdee8: preflight passed`. This includes the server preflight, DAG and split checks. The repaired candidate has ten proof steps, one new unsplit node and zero new Mathlib leaves. Exact citation quotes and an unchanged item statement were checked. A dependency traversal of the sandbox overlay reaches 121 nodes without a cycle. This success supersedes the previous attempt's cycle failure. No push was made. The final report is included in a second dry run before handoff.

## Second reading by Q19

- Item statement: checked every hypothesis and conclusion against the imported item and Cisinski Theorem 7.9.8 conservativity passage; verdict sound and unchanged.
- Step 1: checked the lifting-class closure statement and the pointwise WFS consequences, including identities, composition, pushout/pullback, and functorial replacement; verdict elementary and supported.
- Step 2: checked the pointwise factorization, pushout and pullback constructions and the cofibrant replacement of the raw pullback; verdict hypotheses and directions are correct, with no properness assumption.
- Step 3: checked the finite-word fraction induction, both square equations, and the outer weak-equivalence factors; verdict explicit and non-circular.
- Step 4: checked essential-surjectivity endpoint conjugation and the ordinary homotopy-category comparison; verdict the cited node supplies the stated representation of the actual arrow class.
- Step 5: checked the ordinary localization functor, naturality, and passage from invertible outer factors to each component localization; verdict supported by the comparison node.
- Step 6: checked cofibrant/fibrant replacements, the factorization $Ru=j p$, bifibrancy of $E$, and the exact hypotheses of map-surjectivity; verdict valid.
- Step 7: checked the fold cylinder, diagonal path object, lifting square, and construction of the strict section $t$; verdict all good-cylinder hypotheses and compositions are explicit.
- Step 8: checked the second cylinder argument, two-out-of-three deductions, and both arrow-retract squares recovering $p$, $Ru$, and $u$ in $W$; verdict valid.
- Step 9: checked inversion of all three fraction factors and the equivalence-edge criterion; verdict conclusion follows for the original endpoint-conjugated arrow.
- Step 10: checked the componentwise transformation criterion and the empty-index case; verdict correctly identifies conservativity, including $I=\varnothing$.
- New node `lem-coef-localization-homotopy-category`: checked self-contained definitions, Cisinski source, blueprint ancestry, four search records, small cases (empty, terminal, singleton, discrete, arrow, isomorphisms, and all arrows), and distinction from existing localization nodes; verdict proper independent unsplit prerequisite.

No mathematical or statement repair was required. I changed only this report by adding this second-reading record. The required dry run was rerun after review and passed: `OK (not pushed) deliver/Q19/lem-coef-strict-diagram-evaluation-conservative at 42a6b84118: preflight passed`.
