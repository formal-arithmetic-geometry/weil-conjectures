# Worker report: lem-coef-dg-module-base-change

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-module-base-change.json` (repaired split; statement unchanged).
- `dag/nodes/sec-six-functors/lem-coef-dg-semi-free-cofibrant.json` (new unsplit statement node; Mathlib searches: no match).
- `dag/nodes/sec-six-functors/lem-coef-dg-filtered-quasi-iso.json` (new unsplit statement node; Mathlib searches: no match).
- `citations.json` (verbatim citations for every step and cited node).
- `report.md` (this report).

## Attachments

None. The item has no sorry-free declaration in the inspected source checkouts.

## WANTED

WANTED: Bertrand Toën, “The homotopy theory of dg-categories and derived Morita theory”, Sections 3–4, for the scalar-extension and dg-module model assertions (the URL is cited in the item but the paper is absent from the local literature).

## What was wrong and what changed

The returned version had a 2526-character step 4. It combined the semi-free cell presentation and projective cofibrancy argument, the filtered unit induction, and the passage from cofibrant to arbitrary modules. I split these hidden lemmas into two statement-only nodes: `lem-coef-dg-semi-free-cofibrant` states the cell presentation and projective cofibrancy of semi-free modules, and `lem-coef-dg-filtered-quasi-iso` states the exhaustive graded-piece criterion for quasi-isomorphisms. The item now has four short steps in that location, each citing the precise statement it uses; its statement, hypotheses, route, and all other proof steps are unchanged. I searched the whole DAG and blueprint first. The existing `lem-coef-dg-semi-free-homotopically-projective` is a different conclusion (homotopical projectivity), and `lem-coef-dg-two-sided-bar-derived-tensor` concerns balanced tensors, so neither duplicates either new node.

## What remains unfinished

The two new nodes are intentionally unsplit stage-1 statements and join the queue. No Lean code was written and no compiler, Lake, or build tool was run.

## Review by Q87

I reread the item statement, all eleven proof steps, the current blueprint paragraph 2, and every cited node statement. The local literature lacks Toën, so the proof retains agent provenance and the WANTED entry; Toën Section 3 was also inspected online as a comparison source. The statement remains byte-for-byte unchanged. Steps 1–3 still use the enriched projective diagram model, dg-category composition/semi-free replacement, and derived-adjunction interface exactly as their statements provide. The former step 4 is now steps 4–7: step 4 takes the semi-free replacement and the new node’s projective-cofibrancy assertion; step 5 takes only the replacement, enriched free diagram, and the displayed unit filtration; step 6 takes the new filtered quasi-isomorphism criterion, whose statement explicitly matches the cone filtration argument; step 7 takes the derived-adjunction theorem for the cofibrant-to-arbitrary passage. Each citation quote in `citations.json` is copied verbatim from the cited node statement.

I checked the hypotheses at the split point: the filtration starts at zero, is graded-split and exhaustive, the quotient maps are the local quasi-isomorphisms supplied by quasi-equivalence, and the union argument uses finite support exactly as stated in the new filtered criterion. I tested the split on the empty filtration, identity dg functor, one-object dg rings, and the zero/acyclic quotient cases. The two new statements were searched with LeanFinder, Loogle, and Mathlib grep using the queries recorded in their `mathlib_searches`; LeanSearch was additionally attempted and recorded unavailable because of the provider rate limit. No SGA source was used. The prior return’s only numbered issue, the long non-elementary step 4, is repaired by these two nodes and the four short replacement steps.

## Not duplicates

lem-coef-dg-semi-free-cofibrant vs lem-coef-dg-semi-free-homotopically-projective: the former identifies sphere/disk cell attachments and projective model cofibrancy; the latter only concludes that Hom into acyclic modules is acyclic.
lem-coef-dg-filtered-quasi-iso vs lem-pc-filtered-free-kprojective-stage: the former compares two exhaustive filtered complexes by quotient quasi-isomorphisms; the latter concerns K-projectivity of finite free filtration stages.
lem-coef-dg-filtered-quasi-iso vs lem-kun-filtered-tensor-graded-comparison: that node identifies graded tensor complexes for finite decreasing flat filtrations and does not give the exhaustive increasing filtration quasi-isomorphism criterion.

The original sphere/disk argument remains available in the repository's returned item proof. For the new cofibrancy node, a graded quotient generator lifts to e with de in the preceding stage; attaching the corresponding representable sphere-to-disk cell reconstructs that stage. Compatible lifts against trivial fibrations extend over the countable union. For the filtered criterion, apply the cycle/subtract-lifted-boundary argument to successive cone quotients, starting from zero; at the exhaustive union each cycle belongs to a finite stage. Neither extraction restates a conclusion of the item.

Step 8 uses the dg-category quasi-equivalence definition for H^0 essential surjectivity, and the replacement and derived-adjunction statements for the counit calculation. Step 9 uses the enriched diagram theorem's closure, enriched naturality, free diagram, and evaluation clauses; its Hom-cofibrancy hypothesis is exactly the item's hypothesis on C. Step 10 uses semi-free replacement specialized to the one-object category Z[0]; step 11 uses the dg-category model theorem's explicit local homotopical-flatness clause. These retained arguments are unchanged apart from the internal step numbers. The new filtered node now specifies abelian-group coefficients and removes irrelevant module-replacement statement dependencies. The search log's second phrasings and unavailable LeanSearch results have been copied into both new nodes, without rerunning or inventing searches. No non-elementary step exceeds 2000 characters.

The first dry run found missing inline definition citations in the two new statements. Both now explicitly cite their notion dependencies, and citations.json was regenerated. For the two extracted statements, the source is the retained semi-free unit proof and Toën Section 3 (read online, especially Proposition 3.2 and its free-generator argument); the filtered-complex criterion is an agent-supplied auxiliary argument, not an assertion that Toën states it verbatim. Drinfeld Section 14.8 remains an external comparison reference not obtained locally.

## Retained-work audit and final repair

I compared the retained sandbox with the current shared item without running git. The only changed item fields are proof, proof_deps, status and split_report; the statement, statement dependencies, Lean record and inherited audit metadata are unchanged. The current shared proof still contains the original 2526-character step 4. Thus the retained two-node extraction is a substantive repair of that returned proof, rather than a rebase or an unchanged re-push. The required first dry run of the retained repair exited successfully: `OK (not pushed)` at `b3d601d05b`.

I reread the retained search results in searches.jsonl, including both second phrasings. Their hits concern K-projectivity, generic model lifting and individual quasi-isomorphism criteria; none states either new lemma. I reused those logged searches. A fresh read-only search of WeilConjectures for the exact item tag and dg-module/semi-free/quasi-equivalence terminology returned no declaration. I repeated the whole-blueprint semi-free and filtration searches and opened the neighbouring DAG statements: finite filtered-object induction and finite decreasing filtered-complex comparison do not cover this exhaustive increasing union.

I read the current blueprint ancestor proof's reduction/adjunction calculation (paragraph 2) and Toën Section 3 online at https://arxiv.org/html/math/0408337, especially the free-generator proof of Proposition 3.2 and Proposition 3.3. These agree with the retained module base-change route. Neither new node is claimed to be a verbatim theorem of Toën: their precise sphere/disk and exhaustive-cone arguments are the auxiliary arguments extracted from the returned proof. Their proof sketches remain above, outside their statement-only node files. The initial zero filtration, arbitrary integer generator degrees, coproducts and objectwise application are explicit. No boundedness assumption on the complexes, local cofibrancy assumption on the index categories, or flatness assumption on the tensor factor was added.

The one additional correction is in retained step 10: its reference to the old cycle/subtract-boundary induction now explicitly cites lem-coef-dg-filtered-quasi-iso, applied to the map from zero into the tensor-filtered complex. The target filtration is graded-split, exhaustive and starts at zero; its quotients are sums of shifts of the acyclic complex A. The zero filtration in the source meets the criterion as well. This makes the dependency on the extracted induction explicit without changing the complex argument, its route or its conclusion. I added its verbatim citation to citations.json. All other steps retain their existing arguments.

For B1–B10, both new nodes have self-contained statement-only records, inline notion citations, populated blueprint ancestry and real logged searches; neither is an item clause or a finished Lean declaration. For C1–C7, I opened every cited statement and verified the exact clauses listed earlier in this review, and explicitly corrected the step-10 citation just described. For D1–D5, the new nodes concern cell presentations and filtered complexes, while the item still constructs scalar extension, its coherences, the unit/counit, evaluation and tensor comparison. For E1–E6, the replacement, flatness and local-cofibrancy hypotheses are used only where present. In particular the arbitrary tensor factor is never assumed flat. On a zero module or an empty category the cell assertion has no cells; on a one-cell module it is the displayed sphere/disk pushout. For the filtered criterion, the zero sequence and a single nonzero acyclic quotient pass the cone argument, and an arbitrary cycle at the union already lies in one finite stage. Every non-elementary proof step has fewer than 2000 characters.

Additional duplicate distinctions from the refreshed searches:

lem-coef-dg-filtered-quasi-iso vs lem-pc-flat-filtered-complex-comparison: the latter assumes a finite decreasing filtration, bounded-below complexes and flat ring base change, and compares spectral-sequence pages; the former concerns exhaustive increasing filtrations of unbounded abelian-group complexes.
lem-coef-dg-filtered-quasi-iso vs lem-sp-finite-filtration-induction: the latter compares finitely filtered objects by actual isomorphisms on graded objects; the former compares cochain complexes by quasi-isomorphisms and allows an infinite exhaustive union.
lem-coef-dg-filtered-quasi-iso vs lem-trf-finite-filtered-graded-exactness: the latter proves exactness/strictness of maps of finitely decreasingly filtered objects; it does not state the increasing exhaustive complex criterion.

## Final continuation audit (2026-10-17)

The retained-work dry run in this continuation exited OK at `7bba71202c`. I again compared the sandbox with the shared returned item: the statement and Lean record agree exactly, while the shared step 4 still contains the original cell/cofibrancy and exhaustive-filtration arguments. I retained their two-node extraction, all logged searches and previous review evidence. Reading every cited statement confirmed the free sphere/disk generators, semi-free replacement, model-derived adjunction, filtered criterion and evaluation hypotheses. I made the quasi-equivalence definition used in step 8 an explicit proof citation of `lem-coef-dgcat-model-structure` and added its exact statement sentence to citations.json. I removed the accidentally duplicated acyclicity sentence in step 10; no argument or hypothesis changed.

I reread the blueprint ancestor paragraph 2 locally and Toën Section 3 online, especially Propositions 3.2 and 3.3 (https://arxiv.org/html/math/0408337). The helper nodes express arguments extracted from the returned proof, rather than claiming that Toën states these auxiliary lemmas verbatim. Current whole-DAG/blueprint searches still find no duplicate: `lem-pc-derived-total-filtration-exhaustive` and `lem-pc-derived-total-filtration-stable` only construct and exhaust a particular bicomplex filtration; `lem-pc-derived-module-cellular-filtration` constructs a representative, rather than comparing filtered quasi-isomorphisms or proving dg-module cofibrancy. Existing `lem-kun-split-cell-complex-kflat` concludes K-flatness, rather than either new statement. All proof citations have verbatim quotations, the dependency union agrees, and no non-elementary step exceeds 2000 characters. The statement-only helpers remain the only two new nodes, with no Mathlib leaf claimed.
