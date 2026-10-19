## Files written

- dag/nodes/sec-six-functors/lem-sf-integral-compactification-comparison-bridge.json: item, statement unchanged, split into nine steps.
- dag/nodes/sec-six-functors/lem-sf-constant-semilinear-generator-comparison.json: new statement-only tool, unsplit; no Mathlib match. It identifies the proper and open one-letter coefficient comparisons under scalar restriction and fixes their adjunction compatibility. It contains no compactification-composition assertion.
- citations.json: 24 verbatim statement excerpts, one for each step/cited-node pair.

One new node, zero Mathlib leaves. No Lean files, compilation, live-project writes, unit changes or manual git operations.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item's blueprint tag, semilinear systems, strict/constant towers, and compactification comparisons found no declaration stating the item. The ordinary etale LowerShriekFormalismComparison file concerns a different coefficient formalism and supplies no such integral normalization equality. The upstream master is reference material, not evidence of completion.

## WANTED

None. The proof is explicitly agent-written: the blueprint names compatibility with composition, but does not state or prove this bridge. No missing source is being presented as a literature theorem.

## Findings and changes

The item was unsplit and had no previous sandbox copy or report. Its statement already fixes the necessary normalizations; I retained it verbatim, including the identity model F_id = L R with d_id = 1. There is no statement dispute. In particular the equality is not inferred from equality of finite evaluations or faithfulness of termwise scalar restriction. Only H on complete objects is used faithfully, at the end.

The real additional obligation is the one-letter coefficient comparison across the two diagram coefficient categories. I isolated that as lem-sf-constant-semilinear-generator-comparison. Its source records explicitly that Stacks 0E48 is a foundation for the counit-tensor comparison, not a theorem already asserting this strict semilinear/constant-tower equality. The new node has no proof or proof dependencies. The rest of the split keeps the calculations in the item: single-compactification realization, adjunction transpose, recursive word substitution, then proper/open map compatibility. Thus the new node does not repackage the item or one of its conclusions.

The item's historical unit and blueprint ancestor are sk-thm-sf-identification. I read its normalized-trace route, the chapter record, and the current blueprint source fix-lem-exchanges.proof.md Step 5. The bridge is a coefficient-normalization tool for that route, not a replacement of the unit's proof. Off-unit proper/open, diagram and completion tools are declared individually in split_report.tool_uses. No unit record is changed.

## Searches

Before creating the node I searched the whole DAG's statements for semilinear/constant systems, restriction, generators and projection comparisons, and ran blueprint_refs.py searches for compactification comparison, reduction counit, word comparison, coefficient restriction and generator normalization. The blueprint searches found no statement of the new lemma. The closest DAG nodes were opened: generator-reduction-coherence gives a semilinear transpose and semilinear structural squares; semilinear-derived-sections gives models but not their equality with the prescribed constant q; compact-support-condensed-realization concerns rational condensed realization; semilinear-proper-open-mate-pasting identifies the interchange map, rather than these reduction generators. The source-tag overlaps are compared below.

Ten actual msearch.py commands are logged in searches.jsonl, five for the item and five for the new lemma (two semantic phrasings, Loogle, LeanSearch and a source grep in each set). I read their output. No service was unavailable. The new lemma's grep hit is the underived PresheafOfModules.pushforward definition in Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:89-90; I read lines 60-105. This does not give a derived diagram-site comparison or completion normalization. Loogle returned ordinary adjunction/counit/triangle identities, and LeanFinder/LeanSearch returned ordinary scalar restriction, adic completions, local cohomology, condensed counits and abstract derived-adjunction formulas. I read the derived-adjunction construction in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean and the triangle/transpose interfaces in CategoryTheory/Adjunction/Basic.lean. These support elementary formal calculations but do not construct the ringed-diagram comparison required by the new node. Queries and actual hit summaries are recorded without inventing a search or an absence claim from a failed service.

## Not duplicates

lem-sf-constant-semilinear-generator-comparison vs lem-sf-generator-reduction-coherence: the existing lemma gives r_A = e R(d_A^-1) within semilinear systems and semilinear generator squares; the new lemma identifies r_A with the specified constant-tower q_A after restriction.

lem-sf-constant-semilinear-generator-comparison vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement is the projection/exchange square for four ringed topoi; it does not identify the two coefficient-system reduction generators or the completed-open unit.

lem-sf-constant-semilinear-generator-comparison vs lemma-weil-pbc-completed-exchange-coherence: the existing statement is naturality, identity and pasting for completed exchange, not the scalar-restriction identification of one-letter q and r.

lem-sf-constant-semilinear-generator-comparison vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing construction uses strict towers over the completed coefficient sheaf and compares an ordered pullback/direct-image exchange; the new lemma uses module systems over the varying quotient ring system, and includes completed open extension. Its proper/open generator comparison is not a specialization of that exchange theorem.

lem-sf-constant-semilinear-generator-comparison vs lem-weil-pbc-finite-level-rectangle: the existing statement is a finite-level rectangle identity, not a comparison of strict diagram transformations across the two coefficient categories.

lem-sf-constant-semilinear-generator-comparison vs def-weil-pbc-ringed-tensor-square-presentation: the existing node defines a representative presentation of ringed squares; it asserts no generator normalization under scalar restriction.

lem-sf-constant-semilinear-generator-comparison vs lem-pur-projection-comparison-etale-origin: the existing lemma compares finite etale and pro-etale compact-support projection maps; it neither changes from semilinear to constant towers nor fixes a completion unit.

lem-sf-constant-semilinear-generator-comparison vs lem-sp-compact-projection-base-change: the existing lemma is compatibility of compact-support projection and geometric base change at finite coefficients or varying towers; it does not compare those towers with constant-coordinate reduction generators.

lem-sf-constant-semilinear-generator-comparison vs lem-sp-completion-mate-comparison: the existing statement identifies a completed exchange mate with its constant-tower construction; it has no varying-quotient semilinear system category or open-extension generator comparison.

lem-sf-constant-semilinear-generator-comparison vs lem-amb-shriek-tensor-composition: the existing statement is projection/composition compatibility in ordinary finite etale categories, not the one-letter scalar-restriction comparison at integral coefficients.

lem-sf-constant-semilinear-generator-comparison vs lem-amb-shriek-projection-open-restriction: the existing statement is geometric open-base-restriction compatibility of finite etale compact-support projection, not a change of coefficient-system category.

lem-sf-constant-semilinear-generator-comparison vs lem-pur-co-smooth-pf-exchange-coherence: the existing statement is projection/exchange compatibility for a finite coefficient ring, not strict-system coefficient restriction or completion normalization.

lem-sf-constant-semilinear-generator-comparison vs lem-pur-finite-forward-product-symmetry: the existing statement is symmetry of a finite compact-support external-product transformation; no q/r generator comparison is asserted.

## Review by NY

I read the chapter and unit records and the current main-20261015 fix-lem-exchanges.proof.md Step 5. The blueprint only calls for independence and compatibility with the composition law, so I marked the explicit calculation as an agent proof. For foundations I read sites-cohomology.tex Tag 0941, lemma-derived-limit-is-ok, including its strict K-injective inverse-system model; Tag 0E48, remark-compatible-with-diagram, including its exact counit-tensor projection square and its omitted verification; and the ringed adjunction statement at lemma-adjoint. I also read more-etale.tex Tag 0F7B, lemma-shriek-proper-and-open, with its torsion/bounded-below limitations. I do not attribute the enhanced pro-etale/semilinear extension to that etale source: the actual extensions are supplied by the existing DAG statements. For the new lemma I read 0E48 against the single-letter q normalization in cbc-compact-support-composition-limit, the r normalization in generator-reduction-coherence, and the open completion-unit formula in integral-open-reduction-comparison and cbc-extension-zero-completion. The new assertion is exactly the missing equality between these fixed diagram-site generators; it adds no compactification-composition result.

For Step 1 I checked the constant-completion-equivalence statement actually carries quotient completion units and derived limits to constant coordinates; the new lemma supplies the equality of one-letter r and q as strict-tower maps. For Step 2 I checked generator-reduction-coherence states r_A = e R(d_A^-1), and derived-system-evaluation-calculus states the actual adjunction and triangle identities. The displayed cancellation is unit naturality followed by the right triangle. The proper comparison uses ringed-tower-pushforward-limit-comparison, whose statement gives a natural map for arbitrary ringed topoi, normalized by the common composite direct image, and the word-comparison statement explicitly identifies the one-letter a with it.

For Step 3 I checked integral-open-reduction-comparison supplies the specified d_j and completeness of j_!M. The definition of integral compact support uses the same compactification and quotient transitions, so its comparison after Rp_* is b_p Rp_*(d_j^-1), as fixed by the item. The written naturality calculation proves that the composite r_p/r_j is the transpose of this direct d_v^-1; the inverse adjunction bijection gives exactly e R(d_v^-1). I did not cite the vague expression-realization family c_V to assert that its component is this d_v. For Step 4 I checked the exact recursive equation for q in cbc-compact-support-composition-limit and applied the new lemma twice, so equality is of composed tower maps. Step 5 writes the complete unit/counit cancellation again and proves a_v = H(d_v^-1), rather than identifying their finite reductions. Step 6 uses the same recursive equation at the allowed input F_fK and explicitly expands r_f into its two counit-formula factors; no new comparison lemma is hidden in this substitution.

For Step 7 I checked integral-compactification-system-realization explicitly says restriction of Gamma_Q is the normalized constant-tower map, and semilinear-proper-open-mate-pasting repeats that assertion for the intrinsic mate. The new lemma supplies preservation of the one-letter adjunction data; ambient-proper-open-pasting defines the compositors by their adjunction conjugates, and the actual mate-pasting statement gives the scalar/compositor compatibility. Thus the beta comparison is in the strict derived categories, not deduced from evaluation. In Step 8 the formula for alpha is supplied by the item itself. Substitution gives the requested expression, and the constant-completion equivalence is faithful precisely on the complete source and target. Step 9 checks the identity compactification without changing F_id to Id: e_RM R(u_M)=1 and L(e_RM)u_LRM=1 give the correct transported empty-word normalization. An empty open and a zero input give zero objects and the unique corresponding morphism.

I checked all scheme maps used in proper/open operations are the supplied proper or quasi-compact open maps between separated finite-type schemes, with ell invertible. The hypotheses on compatible witnesses, normalized systems, and common finite cohomological/Tor intervals are retained for every intermediate object, especially F_fK in Step 6. The DVR coefficient specialization supplies the finite perfect quotients required by the constant-tower word theorem. No arbitrary unbounded-system effectivity, finite evaluation faithfulness, or faithfulness of scalar restriction is used. Small cases for the new lemma were an identity proper map, identity/empty open, M = 0, and the terminal scheme with a finite free R-complex: its formula is respectively the reduction identity or the ordinary quotient/projection formula. None introduces a nontrivial automorphism or excludes t-torsion objects; all reductions remain derived.

I checked B1-B9 (statement-only new node, all objects and bounds introduced, definition dependencies, source tag and label, genuine logged searches, blueprint ancestry and duplicate search), C1-C8 (every non-elementary input is a cited statement and every quote was checked as a substring; no dependency path returns to the item; off-unit tools declared), D1-D5 (the item carries the composite and transpose arguments and the helper is confined to generators), and E1-E7 (bounds, coefficient categories, identity normalization and the actual maps). No non-elementary step exceeds 2000 characters. During this review I made the preservation of single-letter adjunction units/counits explicit in the new node and added the mate-pasting citation to Step 7; this closes the otherwise implicit compositor comparison. I also replaced generic closing-sentence quotes by the actual generator equality in citations.json. No statement correction was necessary.

## Validation and remaining work

The server-side review_split check passed on the draft. The full deliver.py --no-push process then exited successfully and printed OK (not pushed) at be60c989cf: preflight passed. This includes server-side DAG/split validation, citation excerpts, logged searches and duplicate checks. There is no unfinished item-level argument; the one new statement-only node is intentionally left unsplit for the next DAG level. The delivery is submitted for the maintainer's independent review.
